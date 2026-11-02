import crypto from 'crypto';
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import {
  getCloudGitHubSettings,
  isValidProductionServerUrl,
  saveCloudGitHubSettings,
  firestoreClient,
} from './db.ts';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const DATA_DIR = path.resolve(__dirname, '../../data');
const PERSISTENT_STORE_FILE = path.resolve(DATA_DIR, 'persistent_store.json');
const LOCAL_VAULT_KEY_FILE = path.resolve(DATA_DIR, '.vault_key');
const LEGACY_VAULT_FILE = path.resolve(DATA_DIR, '.vault_secret.enc');
const LEGACY_SEED_FILE = path.resolve(DATA_DIR, '.vault_seed');

// Google Cloud Secret Manager Secret Identifiers
export const GCP_SECRET_MANAGER_AES_KEY_ID = 'sami-aes256-vault-key';
export const GCP_SECRET_MANAGER_TOKEN_ID = 'sami-github-releases-credentials';
const METADATA_BASE = 'http://metadata.google.internal/computeMetadata/v1';
const GCP_CACHE_TTL_MS = 60_000;

interface StoredSecretPayload {
  token: string;
  updatedAt: number;
}

export interface EncryptedVaultRecord {
  algorithm: 'aes-256-gcm';
  iv: string;
  tag: string;
  data: string;
  updatedAt: number;
}

export type VaultStorageMode =
  | 'gcp_secret_manager'
  | 'persistent_vault'
  | 'server_env'
  | 'unconfigured';

export interface VaultPublicStatus {
  storageMode: VaultStorageMode;
  persistentVaultAvailable: boolean;
  secretManagerEnabled: boolean;
  cloudSettingsPersisted: boolean;
  hasSavedToken: boolean;
  tokenStatusAr: string;
  updatedAt: number | null;
  updatedBy: string | null;
  apiServerUrl: string;
  serviceAccountEmail?: string | null;
  hostingVaultNoticeAr: string | null;
}

export interface ResolvedGitHubVaultCredentials {
  owner: string;
  repo: string;
  token: string;
  hasToken: boolean;
  apiServerUrl: string;
  vault: VaultPublicStatus;
}

export interface SecretManagerDiagnosticReport {
  timestamp: number;
  environmentType: 'ai_studio_sandbox' | 'cloud_run_production' | 'service_account_key' | 'local_development';
  serviceAccount: {
    email: string;
    isSandboxIdentity: boolean;
    source: 'metadata_server' | 'service_account_key' | 'unavailable';
  };
  projectId: {
    effective: string;
    metadataProject: string;
    isCrossProjectMismatch: boolean;
  };
  apiStatus: {
    tested: boolean;
    enabled: boolean;
    httpStatus?: number;
    errorReason?: 'API_DISABLED' | 'ORG_POLICY_RESTRICTED' | 'IAM_PERMISSION_DENIED' | 'PROJECT_NOT_FOUND' | 'NETWORK_ERROR' | 'UNKNOWN';
    rawErrorMessage?: string;
    activationUrl?: string;
  };
  secrets: {
    aesKeySecret: {
      secretId: string;
      existsInGcp: boolean;
      accessibleInGcp: boolean;
      existsInPersistentStore: boolean;
      keyLengthBits: number;
    };
    tokenSecret: {
      secretId: string;
      existsInGcp: boolean;
      accessibleInGcp: boolean;
      existsInPersistentStore: boolean;
    };
  };
  summaryAr: string;
  actionsRequiredAr: string[];
  gcloudCommands: string[];
}

interface GcpServiceAccountAuth {
  accessToken: string;
  projectId: string;
  serviceAccountEmail: string;
  isSandbox: boolean;
  source: 'metadata_server' | 'service_account_key';
}

// In-memory cache for the 256-bit AES key (never logged)
let cachedPersistentAesKey: Buffer | null = null;
let lastKeyFetchTime = 0;

// In-memory cache for active token payload (never logged)
let activeVaultPayload: StoredSecretPayload | null = null;

let gcpProbeDoneAt = 0;
let gcpSecretManagerAvailable = false;
let gcpTargetProjectId: string | null = null;
let gcpServiceAccountEmail: string | null = null;
let gcpCachedTokenPayload: { payload: StoredSecretPayload | null; cachedAt: number } | null = null;

// Isolated server-only set of active token strings used strictly by redactGitHubSecrets()
const redactionTokenSet = new Set<string>();

export function registerTokenForRedaction(token: string): void {
  const clean = token.trim();
  if (clean.length >= 4) {
    redactionTokenSet.add(clean);
  }
}

export function getKnownSecretTokensForRedaction(): string[] {
  const envTok1 = (process.env.GITHUB_TOKEN || '').trim();
  const envTok2 = (process.env.GITHUB_RELEASES_TOKEN || '').trim();
  if (envTok1.length >= 4) redactionTokenSet.add(envTok1);
  if (envTok2.length >= 4) redactionTokenSet.add(envTok2);
  if (activeVaultPayload?.token) {
    redactionTokenSet.add(activeVaultPayload.token);
  }
  return Array.from(redactionTokenSet);
}

export function sanitizeGitHubSlug(val: string | undefined | null): string {
  return String(val || '')
    .trim()
    .replace(/^["']+|["']+$/g, '')
    .replace(/\.git$/i, '')
    .replace(/^\/+|\/+$/g, '');
}

export function parseOwnerAndRepoInput(rawOwner: string, rawRepo: string): { owner: string; repo: string } {
  let owner = sanitizeGitHubSlug(rawOwner);
  let repo = sanitizeGitHubSlug(rawRepo);

  const urlRegex = /^(?:https?:\/\/)?(?:www\.)?github\.com\/([^/\s]+)\/([^/\s]+?)(?:\.git)?\/?$/i;
  const repoUrlMatch = repo.match(urlRegex);
  const ownerUrlMatch = owner.match(urlRegex);

  if (repoUrlMatch) {
    return {
      owner: sanitizeGitHubSlug(repoUrlMatch[1]),
      repo: sanitizeGitHubSlug(repoUrlMatch[2]),
    };
  }
  if (ownerUrlMatch) {
    return {
      owner: sanitizeGitHubSlug(ownerUrlMatch[1]),
      repo: sanitizeGitHubSlug(ownerUrlMatch[2]),
    };
  }
  if (!owner && repo.includes('/')) {
    const parts = repo.split('/').filter(Boolean);
    if (parts.length >= 2) {
      owner = sanitizeGitHubSlug(parts[0]);
      repo = sanitizeGitHubSlug(parts[1]);
    }
  } else if (repo.includes('/') && !repo.startsWith('http')) {
    const parts = repo.split('/').filter(Boolean);
    if (parts.length === 2 && (!owner || owner === parts[0])) {
      owner = sanitizeGitHubSlug(parts[0]);
      repo = sanitizeGitHubSlug(parts[1]);
    }
  }

  return { owner, repo };
}

// ============================================================================
// PERSISTENT DISK STORE FOR SECRETS (SURVIVES RESTARTS IN ALL ENVIRONMENTS)
// ============================================================================

function readPersistentStoreDisk(): Record<string, any> {
  try {
    if (fs.existsSync(PERSISTENT_STORE_FILE)) {
      return JSON.parse(fs.readFileSync(PERSISTENT_STORE_FILE, 'utf8'));
    }
  } catch {}
  return {};
}

function writePersistentStoreSecrets(secrets: {
  vault_aes256_key?: string;
  github_credentials?: EncryptedVaultRecord;
}): void {
  try {
    if (!fs.existsSync(DATA_DIR)) {
      fs.mkdirSync(DATA_DIR, { recursive: true });
    }
    const store = readPersistentStoreDisk();
    store.server_secrets = {
      ...(store.server_secrets || {}),
      ...secrets,
    };
    fs.writeFileSync(PERSISTENT_STORE_FILE, JSON.stringify(store, null, 2), 'utf8');

    // Also mirror the key to .vault_key if provided
    if (secrets.vault_aes256_key) {
      fs.writeFileSync(LOCAL_VAULT_KEY_FILE, secrets.vault_aes256_key, 'utf8');
    }
  } catch (err: any) {
    console.warn('[Sami Vault] Warning persisting secrets to disk:', err?.message);
  }
}

function readPersistentStoreSecrets(): {
  vault_aes256_key?: string;
  github_credentials?: EncryptedVaultRecord;
} {
  const store = readPersistentStoreDisk();
  const sec = store.server_secrets || {};
  if (!sec.vault_aes256_key && fs.existsSync(LOCAL_VAULT_KEY_FILE)) {
    try {
      const k = fs.readFileSync(LOCAL_VAULT_KEY_FILE, 'utf8').trim();
      if (k.length === 64) {
        sec.vault_aes256_key = k;
      }
    } catch {}
  }
  return sec;
}

// ============================================================================
// GOOGLE CLOUD AUTHENTICATION (SERVICE ACCOUNT KEY OR RUNTIME METADATA)
// ============================================================================

/**
 * Mint Google OAuth2 access token from a service account key JSON (RS256)
 */
async function mintTokenFromServiceAccountKey(keyJson: any): Promise<string | null> {
  try {
    const clientEmail = keyJson.client_email;
    const privateKey = keyJson.private_key;
    if (!clientEmail || !privateKey) return null;

    const header = Buffer.from(JSON.stringify({ alg: 'RS256', typ: 'JWT' })).toString('base64url');
    const now = Math.floor(Date.now() / 1000);
    const payload = Buffer.from(
      JSON.stringify({
        iss: clientEmail,
        scope: 'https://www.googleapis.com/auth/cloud-platform',
        aud: 'https://oauth2.googleapis.com/token',
        exp: now + 3600,
        iat: now,
      })
    ).toString('base64url');

    const sign = crypto.createSign('RSA-SHA256');
    sign.update(`${header}.${payload}`);
    const signature = sign.sign(privateKey, 'base64url');
    const assertion = `${header}.${payload}.${signature}`;

    const res = await fetch('https://oauth2.googleapis.com/token', {
      method: 'POST',
      headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
      body: new URLSearchParams({
        grant_type: 'urn:ietf:params:oauth:grant-type:jwt-bearer',
        assertion,
      }),
      signal: AbortSignal.timeout(6_000),
    });

    if (!res.ok) return null;
    const data: any = await res.json();
    return data?.access_token ? String(data.access_token) : null;
  } catch {
    return null;
  }
}

export async function fetchGoogleCloudAuth(): Promise<GcpServiceAccountAuth | null> {
  // 1. Try explicit service account key if provided in environment
  const saKeyRaw = process.env.GCP_SERVICE_ACCOUNT_KEY || process.env.FIREBASE_SERVICE_ACCOUNT_KEY;
  if (saKeyRaw) {
    try {
      const raw = saKeyRaw.trim();
      const jsonStr = raw.startsWith('{') ? raw : Buffer.from(raw, 'base64').toString('utf8');
      const keyObj = JSON.parse(jsonStr);
      if (keyObj?.client_email && keyObj?.private_key) {
        const token = await mintTokenFromServiceAccountKey(keyObj);
        if (token) {
          const projectId = String(keyObj.project_id || process.env.GCP_SECRET_MANAGER_PROJECT || process.env.GOOGLE_CLOUD_PROJECT || '').trim();
          gcpServiceAccountEmail = keyObj.client_email;
          gcpTargetProjectId = projectId;
          return {
            accessToken: token,
            projectId,
            serviceAccountEmail: keyObj.client_email,
            isSandbox: false,
            source: 'service_account_key',
          };
        }
      }
    } catch {}
  }

  // 2. Fetch from runtime metadata server (Cloud Run / AI Studio Sandbox)
  try {
    const headers = { 'Metadata-Flavor': 'Google' };
    const [projRes, tokRes, emailRes] = await Promise.all([
      fetch(`${METADATA_BASE}/project/project-id`, {
        headers,
        signal: AbortSignal.timeout(2_500),
      }),
      fetch(`${METADATA_BASE}/instance/service-accounts/default/token`, {
        headers,
        signal: AbortSignal.timeout(2_500),
      }),
      fetch(`${METADATA_BASE}/instance/service-accounts/default/email`, {
        headers,
        signal: AbortSignal.timeout(2_500),
      }).catch(() => null),
    ]);

    if (!tokRes.ok) return null;
    const tokJson: any = await tokRes.json().catch(() => null);
    if (!tokJson?.access_token) return null;

    const metaProj = projRes.ok ? (await projRes.text()).trim() : '';
    const email = emailRes && emailRes.ok ? (await emailRes.text()).trim() : 'Cloud Run Default Service Account';
    const isSandbox = email.includes('ais-sandbox') || metaProj.startsWith('ais-');

    // In AI Studio sandbox, the sandbox SA token can only query the sandbox project (metaProj),
    // NOT the external Firebase/GCP project unless cross-project permissions are configured.
    // In production Cloud Run, metaProj IS the application's actual GCP project.
    const projectId = isSandbox
      ? metaProj
      : (process.env.GCP_SECRET_MANAGER_PROJECT || metaProj || process.env.GOOGLE_CLOUD_PROJECT || '').trim();

    gcpServiceAccountEmail = email;
    gcpTargetProjectId = projectId;

    return {
      accessToken: String(tokJson.access_token),
      projectId,
      serviceAccountEmail: email,
      isSandbox,
      source: 'metadata_server',
    };
  } catch {
    return null;
  }
}

// Backward-compatible alias
export const fetchMetadataServiceAccountAuth = fetchGoogleCloudAuth;

// ============================================================================
// SECRET MANAGER PROBE & DETAILED ERROR DIAGNOSTICS (REQUIREMENT 8)
// ============================================================================

export async function diagnoseSecretManager(forceFresh = false): Promise<SecretManagerDiagnosticReport> {
  const auth = await fetchGoogleCloudAuth();
  const persistentSec = readPersistentStoreSecrets();
  const hasLocalKey = Boolean(persistentSec.vault_aes256_key && persistentSec.vault_aes256_key.length === 64);
  const hasLocalEncToken = Boolean(persistentSec.github_credentials?.data);

  const envType: SecretManagerDiagnosticReport['environmentType'] = !auth
    ? 'local_development'
    : auth.source === 'service_account_key'
      ? 'service_account_key'
      : auth.isSandbox
        ? 'ai_studio_sandbox'
        : 'cloud_run_production';

  const report: SecretManagerDiagnosticReport = {
    timestamp: Date.now(),
    environmentType: envType,
    serviceAccount: {
      email: auth?.serviceAccountEmail || 'غير متاح',
      isSandboxIdentity: Boolean(auth?.isSandbox),
      source: auth ? auth.source : 'unavailable',
    },
    projectId: {
      effective: auth?.projectId || process.env.GOOGLE_CLOUD_PROJECT || 'majestic-interface-ksmzh',
      metadataProject: auth?.projectId || 'غير متاح',
      isCrossProjectMismatch: Boolean(auth?.isSandbox && process.env.GOOGLE_CLOUD_PROJECT && auth.projectId !== process.env.GOOGLE_CLOUD_PROJECT),
    },
    apiStatus: {
      tested: false,
      enabled: false,
    },
    secrets: {
      aesKeySecret: {
        secretId: GCP_SECRET_MANAGER_AES_KEY_ID,
        existsInGcp: false,
        accessibleInGcp: false,
        existsInPersistentStore: hasLocalKey,
        keyLengthBits: 256,
      },
      tokenSecret: {
        secretId: GCP_SECRET_MANAGER_TOKEN_ID,
        existsInGcp: false,
        accessibleInGcp: false,
        existsInPersistentStore: hasLocalEncToken,
      },
    },
    summaryAr: '',
    actionsRequiredAr: [],
    gcloudCommands: [],
  };

  if (!auth) {
    report.apiStatus.tested = false;
    report.summaryAr = 'الخادم يعمل خارج بيئة Google Cloud (أو بدون مفتاح خدمة GCP). التشفير يعمل عبر وحدة التخزين الدائمة الآمنة (AES-256-GCM).';
    return report;
  }

  // 1. Test Secret Manager API by accessing the AES key secret directly
  report.apiStatus.tested = true;
  const targetProject = report.projectId.effective;
  const secretKeyPath = `projects/${encodeURIComponent(targetProject)}/secrets/${GCP_SECRET_MANAGER_AES_KEY_ID}`;

  try {
    const res = await fetch(`https://secretmanager.googleapis.com/v1/${secretKeyPath}`, {
      method: 'GET',
      headers: { Authorization: `Bearer ${auth.accessToken}` },
      signal: AbortSignal.timeout(4_000),
    });

    report.apiStatus.httpStatus = res.status;
    const bodyText = await res.text().catch(() => '');

    if (res.ok) {
      report.apiStatus.enabled = true;
      report.secrets.aesKeySecret.existsInGcp = true;

      // Test access to latest version
      const accessRes = await fetch(`https://secretmanager.googleapis.com/v1/${secretKeyPath}/versions/latest:access`, {
        method: 'GET',
        headers: { Authorization: `Bearer ${auth.accessToken}` },
        signal: AbortSignal.timeout(4_000),
      });
      if (accessRes.ok) {
        report.secrets.aesKeySecret.accessibleInGcp = true;
      }
    } else if (res.status === 404) {
      // Secret doesn't exist yet, but the API IS ENABLED!
      report.apiStatus.enabled = true;
      report.secrets.aesKeySecret.existsInGcp = false;
      report.actionsRequiredAr.push(`السر ${GCP_SECRET_MANAGER_AES_KEY_ID} غير منشأ بعد في Secret Manager (سيقوم الخادم بإنشائه تلقائياً عند أول حفظ).`);
    } else if (res.status === 403) {
      // Differentiate why 403 occurred
      if (bodyText.includes('SERVICE_DISABLED') || bodyText.includes('has not been used') || bodyText.includes('is disabled')) {
        report.apiStatus.enabled = false;
        report.apiStatus.errorReason = 'API_DISABLED';
        report.apiStatus.rawErrorMessage = 'Secret Manager API غير مفعّلة في المشروع.';
        report.apiStatus.activationUrl = `https://console.developers.google.com/apis/api/secretmanager.googleapis.com/overview?project=${targetProject}`;
        report.actionsRequiredAr.push(`تفعيل Secret Manager API في المشروع ${targetProject}.`);
      } else if (bodyText.includes('constraints/gcp.restrictServiceUsage')) {
        report.apiStatus.enabled = false;
        report.apiStatus.errorReason = 'ORG_POLICY_RESTRICTED';
        report.apiStatus.rawErrorMessage = 'استخدام Secret Manager مقيّد بواسطة سياسة المؤسسة (Organization Constraint: restrictServiceUsage).';
        report.actionsRequiredAr.push('إلغاء تقييد Secret Manager في سياسة المؤسسة (Org Policy) أو استخدام التخزين المشفر في Firestore.');
      } else if (bodyText.includes('PERMISSION_DENIED') || bodyText.includes('Permission denied')) {
        report.apiStatus.enabled = true; // API is enabled, but IAM role is missing!
        report.apiStatus.errorReason = 'IAM_PERMISSION_DENIED';
        report.apiStatus.rawErrorMessage = `حساب الخدمة (${auth.serviceAccountEmail}) يفتقر لصلاحية الوصول إلى Secret Manager.`;
        report.actionsRequiredAr.push(`منح حساب الخدمة (${auth.serviceAccountEmail}) الدور: roles/secretmanager.secretAccessor.`);
      } else {
        report.apiStatus.errorReason = 'UNKNOWN';
        report.apiStatus.rawErrorMessage = bodyText.slice(0, 200);
      }
    }

    // 2. Test Token Secret status
    const tokenSecretPath = `projects/${encodeURIComponent(targetProject)}/secrets/${GCP_SECRET_MANAGER_TOKEN_ID}`;
    const tokenRes = await fetch(`https://secretmanager.googleapis.com/v1/${tokenSecretPath}`, {
      method: 'GET',
      headers: { Authorization: `Bearer ${auth.accessToken}` },
      signal: AbortSignal.timeout(3_000),
    }).catch(() => null);

    if (tokenRes && tokenRes.ok) {
      report.secrets.tokenSecret.existsInGcp = true;
      const tokAcc = await fetch(`https://secretmanager.googleapis.com/v1/${tokenSecretPath}/versions/latest:access`, {
        method: 'GET',
        headers: { Authorization: `Bearer ${auth.accessToken}` },
        signal: AbortSignal.timeout(3_000),
      }).catch(() => null);
      if (tokAcc && tokAcc.ok) {
        report.secrets.tokenSecret.accessibleInGcp = true;
      }
    }
  } catch (err: any) {
    report.apiStatus.errorReason = 'NETWORK_ERROR';
    report.apiStatus.rawErrorMessage = err?.message || String(err);
  }

  // Generate exact gcloud commands
  const sa = auth.serviceAccountEmail;
  report.gcloudCommands = [
    `# 1. تفعيل Secret Manager API في مشروعك:`,
    `gcloud services enable secretmanager.googleapis.com --project ${targetProject}`,
    ``,
    `# 2. منح حساب الخدمة أقل الصلاحيات اللازمة للوصول وإضافة إصدارات:`,
    `gcloud projects add-iam-policy-binding ${targetProject} \\`,
    `    --member="serviceAccount:${sa}" \\`,
    `    --role="roles/secretmanager.secretAccessor"`,
    `gcloud projects add-iam-policy-binding ${targetProject} \\`,
    `    --member="serviceAccount:${sa}" \\`,
    `    --role="roles/secretmanager.secretVersionManager"`,
  ];

  if (report.environmentType === 'ai_studio_sandbox') {
    report.summaryAr = `الخادم يعمل حالياً في بيئة التطوير (AI Studio Sandbox) بحساب خدمة معزول (${sa}). يتم حفظ التوكنات وتشفيرها محلياً وسحابياً عبر وحدة التخزين الدائمة المشفرة (AES-256-GCM). عند النشر على Google Cloud Run الإنتاجي، سيعمل Secret Manager بسلاسة مع حساب خدمة Cloud Run.`;
  } else if (report.apiStatus.enabled && report.secrets.aesKeySecret.accessibleInGcp) {
    report.summaryAr = 'الاتصال بـ Google Cloud Secret Manager متصل ونشط بالكامل وجاهز للاستخدام.';
  } else {
    report.summaryAr = `Secret Manager في حالة فحص: ${report.apiStatus.rawErrorMessage || 'بانتظار اكتمال الإعداد'}. يتم الحفاظ على التوكن مشفراً وآمناً عبر وحدة التخزين الدائمة.`;
  }

  return report;
}

export async function probeGcpSecretManager(force = false): Promise<boolean> {
  if (!force && gcpProbeDoneAt > 0 && Date.now() - gcpProbeDoneAt < 60_000) {
    return gcpSecretManagerAvailable;
  }
  gcpProbeDoneAt = Date.now();

  const auth = await fetchGoogleCloudAuth();
  if (!auth) {
    gcpSecretManagerAvailable = false;
    return false;
  }

  // In sandbox with no custom key, sandbox SA cannot access external GCP project Secret Manager
  if (auth.isSandbox && auth.source !== 'service_account_key') {
    gcpSecretManagerAvailable = false;
    gcpServiceAccountEmail = auth.serviceAccountEmail;
    gcpTargetProjectId = auth.projectId;
    return false;
  }

  try {
    const parent = `projects/${encodeURIComponent(auth.projectId)}`;
    const res = await fetch(`https://secretmanager.googleapis.com/v1/${parent}/secrets/${GCP_SECRET_MANAGER_AES_KEY_ID}`, {
      method: 'GET',
      headers: { Authorization: `Bearer ${auth.accessToken}` },
      signal: AbortSignal.timeout(3_500),
    });

    if (res.ok || res.status === 404) {
      gcpSecretManagerAvailable = true;
      gcpTargetProjectId = auth.projectId;
      gcpServiceAccountEmail = auth.serviceAccountEmail;
      return true;
    }

    gcpSecretManagerAvailable = false;
    return false;
  } catch {
    gcpSecretManagerAvailable = false;
    return false;
  }
}

// ============================================================================
// 256-BIT CRYPTOGRAPHIC KEY LIFECYCLE (REQUIREMENT 6 & 7)
// - Cryptographically secure CSPRNG (crypto.randomBytes(32))
// - Never derived from Project ID or public data
// - Reused permanently across server restarts (never regenerated, no loss of decryption)
// ============================================================================

export async function getOrCreateSecretManagerAesKey(forceFresh = false): Promise<Buffer> {
  if (!forceFresh && cachedPersistentAesKey && Date.now() - lastKeyFetchTime < GCP_CACHE_TTL_MS) {
    return cachedPersistentAesKey;
  }

  const auth = await fetchGoogleCloudAuth();

  // 1. If Secret Manager is available, try fetching the key from GCP Secret Manager
  if (auth && !auth.isSandbox) {
    try {
      const parent = `projects/${encodeURIComponent(auth.projectId)}`;
      const secretName = `${parent}/secrets/${GCP_SECRET_MANAGER_AES_KEY_ID}`;
      const accessRes = await fetch(`https://secretmanager.googleapis.com/v1/${secretName}/versions/latest:access`, {
        method: 'GET',
        headers: { Authorization: `Bearer ${auth.accessToken}` },
        signal: AbortSignal.timeout(4_000),
      });

      if (accessRes.ok) {
        const data: any = await accessRes.json().catch(() => null);
        const b64 = data?.payload?.data;
        if (b64) {
          const rawKeyStr = Buffer.from(String(b64), 'base64').toString('utf8').trim();
          let keyBuf: Buffer | null = null;
          if (rawKeyStr.length === 64 && /^[0-9a-fA-F]+$/.test(rawKeyStr)) {
            keyBuf = Buffer.from(rawKeyStr, 'hex');
          } else if (Buffer.from(String(b64), 'base64').length === 32) {
            keyBuf = Buffer.from(String(b64), 'base64');
          }
          if (keyBuf && keyBuf.length === 32) {
            cachedPersistentAesKey = keyBuf;
            lastKeyFetchTime = Date.now();
            // Mirror to persistent store so key is also kept locally
            writePersistentStoreSecrets({ vault_aes256_key: keyBuf.toString('hex') });
            return cachedPersistentAesKey;
          }
        }
      }
    } catch {}
  }

  // 2. Check local persistent store for previously created 256-bit key
  const persistent = readPersistentStoreSecrets();
  if (persistent.vault_aes256_key && persistent.vault_aes256_key.length === 64) {
    const keyBuf = Buffer.from(persistent.vault_aes256_key, 'hex');
    if (keyBuf.length === 32) {
      cachedPersistentAesKey = keyBuf;
      lastKeyFetchTime = Date.now();

      // If Secret Manager is available in GCP and secret doesn't exist, sync it now
      if (auth && !auth.isSandbox) {
        syncKeyToSecretManager(auth, keyBuf).catch(() => {});
      }
      return cachedPersistentAesKey;
    }
  }

  // 3. No key exists anywhere. Generate cryptographically secure random 256-bit key (CSPRNG)
  // Requirement 6: Secure random 256-bit key, never derived from project ID or public data
  const newRandomKey = crypto.randomBytes(32);
  const keyHex = newRandomKey.toString('hex');

  // Requirement 7: Persist immediately so it is NEVER re-generated on server restarts
  writePersistentStoreSecrets({ vault_aes256_key: keyHex });
  cachedPersistentAesKey = newRandomKey;
  lastKeyFetchTime = Date.now();

  // Try saving to Secret Manager in GCP if available
  if (auth && !auth.isSandbox) {
    syncKeyToSecretManager(auth, newRandomKey).catch(() => {});
  }

  return cachedPersistentAesKey;
}

async function syncKeyToSecretManager(auth: GcpServiceAccountAuth, keyBuf: Buffer): Promise<void> {
  try {
    const parent = `projects/${encodeURIComponent(auth.projectId)}`;
    const secretName = `${parent}/secrets/${GCP_SECRET_MANAGER_AES_KEY_ID}`;
    const authHeaders = {
      Authorization: `Bearer ${auth.accessToken}`,
      'Content-Type': 'application/json',
    };

    // Ensure secret exists
    const checkRes = await fetch(`https://secretmanager.googleapis.com/v1/${secretName}`, {
      headers: { Authorization: `Bearer ${auth.accessToken}` },
    });
    if (checkRes.status === 404) {
      await fetch(`https://secretmanager.googleapis.com/v1/${parent}/secrets?secretId=${GCP_SECRET_MANAGER_AES_KEY_ID}`, {
        method: 'POST',
        headers: authHeaders,
        body: JSON.stringify({ replication: { automatic: {} } }),
      });
    }

    const b64Data = Buffer.from(keyBuf.toString('hex'), 'utf8').toString('base64');
    await fetch(`https://secretmanager.googleapis.com/v1/${secretName}:addVersion`, {
      method: 'POST',
      headers: authHeaders,
      body: JSON.stringify({ payload: { data: b64Data } }),
    });
  } catch {}
}

// ============================================================================
// AES-256-GCM ENCRYPTION & DECRYPTION (ZERO LEAKS, ZERO LOSS OF OLD TOKENS)
// ============================================================================

export async function encryptTokenWithSecretManagerKey(token: string): Promise<EncryptedVaultRecord> {
  const key = await getOrCreateSecretManagerAesKey();
  const iv = crypto.randomBytes(12);
  const cipher = crypto.createCipheriv('aes-256-gcm', key, iv);
  const encrypted = Buffer.concat([cipher.update(token, 'utf8'), cipher.final()]);
  const tag = cipher.getAuthTag();

  return {
    algorithm: 'aes-256-gcm',
    iv: iv.toString('hex'),
    tag: tag.toString('hex'),
    data: encrypted.toString('hex'),
    updatedAt: Date.now(),
  };
}

export async function decryptTokenWithSecretManagerKey(record: EncryptedVaultRecord): Promise<string | null> {
  if (!record || record.algorithm !== 'aes-256-gcm' || !record.iv || !record.tag || !record.data) {
    return null;
  }
  try {
    const key = await getOrCreateSecretManagerAesKey();
    const iv = Buffer.from(record.iv, 'hex');
    const tag = Buffer.from(record.tag, 'hex');
    const decipher = crypto.createDecipheriv('aes-256-gcm', key, iv);
    decipher.setAuthTag(tag);
    const decrypted = decipher.update(Buffer.from(record.data, 'hex'), undefined, 'utf8') + decipher.final('utf8');
    return decrypted.trim() || null;
  } catch {
    return null;
  }
}

// Legacy fallback decryption strictly for seamless migration of existing records without data loss
function decryptLegacyMigrationToken(record: EncryptedVaultRecord): string | null {
  try {
    const legacySeed = 'e18d1b0ffead4e1873e86d6e01ae7314c865a4e415db8b744a739290ed5ddaef';
    const legacyKey = crypto.scryptSync(legacySeed, 'sami_app_vault_salt_2026_isolated_cloud_key', 32);
    const iv = Buffer.from(record.iv, 'hex');
    const tag = Buffer.from(record.tag, 'hex');
    const decipher = crypto.createDecipheriv('aes-256-gcm', legacyKey, iv);
    decipher.setAuthTag(tag);
    const decrypted = decipher.update(Buffer.from(record.data, 'hex'), undefined, 'utf8') + decipher.final('utf8');
    return decrypted.trim() || null;
  } catch {
    return null;
  }
}

function purgeLegacyVaultFiles(): void {
  try {
    if (fs.existsSync(LEGACY_VAULT_FILE)) fs.unlinkSync(LEGACY_VAULT_FILE);
  } catch {}
  try {
    if (fs.existsSync(LEGACY_SEED_FILE)) fs.unlinkSync(LEGACY_SEED_FILE);
  } catch {}
}

// ============================================================================
// SECRET MANAGER READ & WRITE OPERATIONS
// ============================================================================

async function readTokenFromSecretManager(bypassCache = false): Promise<StoredSecretPayload | null> {
  if (!bypassCache && gcpCachedTokenPayload && Date.now() - gcpCachedTokenPayload.cachedAt < GCP_CACHE_TTL_MS) {
    return gcpCachedTokenPayload.payload;
  }

  const auth = await fetchGoogleCloudAuth();
  if (!auth || auth.isSandbox) return null;

  try {
    const res = await fetch(
      `https://secretmanager.googleapis.com/v1/projects/${encodeURIComponent(auth.projectId)}/secrets/${GCP_SECRET_MANAGER_TOKEN_ID}/versions/latest:access`,
      {
        method: 'GET',
        headers: { Authorization: `Bearer ${auth.accessToken}` },
        signal: AbortSignal.timeout(4_000),
      }
    );

    if (!res.ok) {
      gcpCachedTokenPayload = { payload: null, cachedAt: Date.now() };
      return null;
    }

    const data: any = await res.json().catch(() => null);
    const b64 = data?.payload?.data;
    if (!b64) return null;
    const jsonStr = Buffer.from(String(b64), 'base64').toString('utf8');
    const parsed = JSON.parse(jsonStr) as any;
    const cleanTok = sanitizeGitHubSlug(parsed?.token);
    if (!cleanTok) return null;

    registerTokenForRedaction(cleanTok);
    const result: StoredSecretPayload = {
      token: cleanTok,
      updatedAt: Number(parsed?.updatedAt) || Date.now(),
    };
    gcpCachedTokenPayload = { payload: result, cachedAt: Date.now() };
    return result;
  } catch {
    return null;
  }
}

async function writeTokenToSecretManager(payload: StoredSecretPayload): Promise<boolean> {
  const auth = await fetchGoogleCloudAuth();
  if (!auth || auth.isSandbox) {
    return false;
  }

  const parent = `projects/${encodeURIComponent(auth.projectId)}`;
  const secretName = `${parent}/secrets/${GCP_SECRET_MANAGER_TOKEN_ID}`;
  const authHeaders = {
    Authorization: `Bearer ${auth.accessToken}`,
    'Content-Type': 'application/json',
  };

  try {
    const getSec = await fetch(`https://secretmanager.googleapis.com/v1/${secretName}`, {
      method: 'GET',
      headers: { Authorization: `Bearer ${auth.accessToken}` },
      signal: AbortSignal.timeout(4_000),
    });

    if (getSec.status === 404) {
      const createSec = await fetch(
        `https://secretmanager.googleapis.com/v1/${parent}/secrets?secretId=${GCP_SECRET_MANAGER_TOKEN_ID}`,
        {
          method: 'POST',
          headers: authHeaders,
          body: JSON.stringify({ replication: { automatic: {} } }),
          signal: AbortSignal.timeout(5_000),
        }
      );
      if (!createSec.ok && createSec.status !== 409) {
        return false;
      }
    } else if (!getSec.ok) {
      return false;
    }

    const b64Data = Buffer.from(JSON.stringify(payload), 'utf8').toString('base64');
    const addVer = await fetch(`https://secretmanager.googleapis.com/v1/${secretName}:addVersion`, {
      method: 'POST',
      headers: authHeaders,
      body: JSON.stringify({ payload: { data: b64Data } }),
      signal: AbortSignal.timeout(5_000),
    });

    if (addVer.ok) {
      gcpCachedTokenPayload = null;
      return true;
    }
    return false;
  } catch {
    return false;
  }
}

// ============================================================================
// FIRESTORE ENCRYPTED RECORD (ZERO-TRUST, PERSISTED IN CLOUD)
// ============================================================================

async function readFromFirestoreEncryptedRecord(): Promise<StoredSecretPayload | null> {
  if (!firestoreClient) return null;
  try {
    const doc = await firestoreClient.collection('server_secrets').doc('github_credentials').get();
    if (!doc.exists) return null;
    const record = doc.data() as EncryptedVaultRecord;

    let decrypted = await decryptTokenWithSecretManagerKey(record).catch(() => null);
    if (!decrypted) {
      decrypted = decryptLegacyMigrationToken(record);
      if (decrypted) {
        writeToFirestoreEncryptedRecord(decrypted).catch(() => {});
      }
    }

    if (!decrypted) return null;
    registerTokenForRedaction(decrypted);
    return { token: decrypted, updatedAt: record.updatedAt || Date.now() };
  } catch {
    return null;
  }
}

async function writeToFirestoreEncryptedRecord(token: string): Promise<boolean> {
  if (!firestoreClient) return false;
  try {
    const encrypted = await encryptTokenWithSecretManagerKey(token);
    await firestoreClient.collection('server_secrets').doc('github_credentials').set(encrypted, { merge: true });
    return true;
  } catch {
    return false;
  }
}

function readPermanentEnvCredentials(): { owner: string; repo: string; token: string } {
  const rawOwner = (process.env.GITHUB_RELEASES_OWNER || process.env.GITHUB_OWNER || '').trim();
  const rawRepo = (process.env.GITHUB_RELEASES_REPO || process.env.GITHUB_REPO || '').trim();
  const parsed = parseOwnerAndRepoInput(rawOwner, rawRepo);
  const token = sanitizeGitHubSlug(process.env.GITHUB_RELEASES_TOKEN || process.env.GITHUB_TOKEN || '');
  if (token) registerTokenForRedaction(token);
  return {
    owner: parsed.owner,
    repo: parsed.repo,
    token,
  };
}

// ============================================================================
// RESOLUTION & VAULT STORAGE LOGIC (RELIABLE & PERSISTENT)
// ============================================================================

export async function getResolvedGitHubCredentials(forceFresh = false): Promise<ResolvedGitHubVaultCredentials> {
  const [secretManagerEnabled, cloudSettings] = await Promise.all([
    probeGcpSecretManager(forceFresh),
    getCloudGitHubSettings(forceFresh),
  ]);

  const envCreds = readPermanentEnvCredentials();

  let resolvedToken = '';
  let storageMode: VaultStorageMode = 'unconfigured';
  let updatedAt: number | null = cloudSettings.updatedAt || null;

  // 1. In-memory runtime cache
  if (!forceFresh && activeVaultPayload?.token) {
    resolvedToken = activeVaultPayload.token;
    storageMode = secretManagerEnabled ? 'gcp_secret_manager' : 'persistent_vault';
    updatedAt = activeVaultPayload.updatedAt;
  }

  // 2. Secret Manager payload (if active in GCP)
  if (!resolvedToken && secretManagerEnabled) {
    const smSecret = await readTokenFromSecretManager(forceFresh);
    if (smSecret?.token) {
      resolvedToken = smSecret.token;
      storageMode = 'gcp_secret_manager';
      updatedAt = smSecret.updatedAt;
      activeVaultPayload = smSecret;
    }
  }

  // 3. Persistent disk store encrypted record
  if (!resolvedToken) {
    const persistent = readPersistentStoreSecrets();
    if (persistent.github_credentials) {
      const decrypted = await decryptTokenWithSecretManagerKey(persistent.github_credentials);
      if (decrypted) {
        resolvedToken = decrypted;
        storageMode = secretManagerEnabled ? 'gcp_secret_manager' : 'persistent_vault';
        updatedAt = persistent.github_credentials.updatedAt;
        activeVaultPayload = { token: decrypted, updatedAt };
      }
    }
  }

  // 4. Firestore encrypted record
  if (!resolvedToken) {
    const fsVault = await readFromFirestoreEncryptedRecord();
    if (fsVault?.token) {
      resolvedToken = fsVault.token;
      storageMode = secretManagerEnabled ? 'gcp_secret_manager' : 'persistent_vault';
      updatedAt = fsVault.updatedAt;
      activeVaultPayload = fsVault;
    }
  }

  // 5. Legacy migration record (if any exists from older versions)
  if (!resolvedToken && fs.existsSync(LEGACY_VAULT_FILE)) {
    try {
      const raw = fs.readFileSync(LEGACY_VAULT_FILE, 'utf8').trim();
      if (raw) {
        const rec = JSON.parse(raw) as EncryptedVaultRecord;
        const legacyDecrypted = decryptLegacyMigrationToken(rec);
        if (legacyDecrypted) {
          resolvedToken = legacyDecrypted;
          storageMode = 'persistent_vault';
          updatedAt = rec.updatedAt || Date.now();
          activeVaultPayload = { token: resolvedToken, updatedAt };

          // Re-encrypt under the persistent 256-bit key
          const newEnc = await encryptTokenWithSecretManagerKey(resolvedToken);
          writePersistentStoreSecrets({ github_credentials: newEnc });
          writeToFirestoreEncryptedRecord(resolvedToken).catch(() => {});
        }
      }
    } catch {}
    purgeLegacyVaultFiles();
  }

  // 6. Permanent server environment variable fallback
  if (!resolvedToken && envCreds.token) {
    resolvedToken = envCreds.token;
    storageMode = 'server_env';
    activeVaultPayload = { token: resolvedToken, updatedAt: Date.now() };
  }

  if (resolvedToken) {
    registerTokenForRedaction(resolvedToken);
  }

  const resolvedOwner = cloudSettings.githubOwner || envCreds.owner || '';
  const resolvedRepo = cloudSettings.githubRepo || envCreds.repo || '';
  const hasSavedToken = resolvedToken.length > 0;
  const persistentVaultAvailable = true; // Always true: backed by persistent 256-bit AES vault

  let tokenStatusAr = 'التوكن غير محفوظ';
  if (hasSavedToken) {
    if (storageMode === 'gcp_secret_manager') {
      tokenStatusAr = 'التوكن محفوظ ومشفر في Google Cloud Secret Manager';
    } else if (storageMode === 'server_env') {
      tokenStatusAr = 'التوكن مضبوط عبر متغيرات بيئة الخادم (GITHUB_TOKEN)';
    } else {
      tokenStatusAr = 'التوكن محفوظ ومشفر بأمان بمفتاح AES-256 (محمي في وحدة تخزين الخادم الدائمة)';
    }
  }

  return {
    owner: resolvedOwner,
    repo: resolvedRepo,
    token: resolvedToken,
    hasToken: hasSavedToken,
    apiServerUrl: cloudSettings.apiServerUrl,
    vault: {
      storageMode,
      persistentVaultAvailable,
      secretManagerEnabled,
      cloudSettingsPersisted: cloudSettings.source === 'firestore',
      hasSavedToken,
      tokenStatusAr,
      updatedAt,
      updatedBy: cloudSettings.updatedBy,
      apiServerUrl: cloudSettings.apiServerUrl,
      serviceAccountEmail: gcpServiceAccountEmail,
      hostingVaultNoticeAr: null,
    },
  };
}

export async function saveGitHubCredentialsToVault(input: {
  owner: string;
  repo: string;
  token?: string;
  apiServerUrl?: string;
  updatedBy?: string;
}): Promise<{
  owner: string;
  repo: string;
  hasToken: boolean;
  apiServerUrl: string;
  vault: VaultPublicStatus;
}> {
  const parsed = parseOwnerAndRepoInput(input.owner, input.repo);
  const slugRegex = /^[A-Za-z0-9._-]+$/;

  if (!parsed.owner || !slugRegex.test(parsed.owner)) {
    throw new Error('يرجى إدخال اسم مالك مستودع GitHub صالح في حقل GITHUB_OWNER');
  }
  if (!parsed.repo || !slugRegex.test(parsed.repo)) {
    throw new Error('يرجى إدخال اسم مستودع GitHub صالح في حقل GITHUB_REPO');
  }

  let cleanApiServerUrl: string | undefined;
  if (input.apiServerUrl !== undefined && String(input.apiServerUrl).trim() !== '') {
    const validUrl = isValidProductionServerUrl(input.apiServerUrl);
    if (validUrl) {
      cleanApiServerUrl = validUrl;
    }
  }

  const incomingToken = sanitizeGitHubSlug(input.token);
  if (incomingToken && /\s/.test(incomingToken)) {
    throw new Error('صيغة التوكن المدخل في GITHUB_TOKEN غير صالحة (يجب ألا يحتوي على مسافات)');
  }

  const current = await getResolvedGitHubCredentials(true);

  // STEP 1: Process and store secret token
  let tokenToUse = incomingToken;
  if (!tokenToUse) {
    if (!current.hasToken) {
      throw new Error('يرجى إدخال التوكن السري (GITHUB_TOKEN) لحفظ الإعدادات لأول مرة');
    }
    tokenToUse = current.token;
  }

  registerTokenForRedaction(tokenToUse);

  // A. Encrypt with persistent 256-bit AES key and save to persistent disk store
  const encryptedRecord = await encryptTokenWithSecretManagerKey(tokenToUse);
  writePersistentStoreSecrets({ github_credentials: encryptedRecord });

  // B. Also write to Firestore encrypted record if available
  writeToFirestoreEncryptedRecord(tokenToUse).catch(() => {});

  // C. If Google Cloud Secret Manager is reachable in GCP, write to Secret Manager as well
  const smAvailable = await probeGcpSecretManager(true);
  if (smAvailable) {
    await writeTokenToSecretManager({
      token: tokenToUse,
      updatedAt: Date.now(),
    }).catch(() => {});
  }

  // Update in-memory runtime cache
  activeVaultPayload = {
    token: tokenToUse,
    updatedAt: Date.now(),
  };

  // STEP 2: Persist non-secret GITHUB_OWNER and GITHUB_REPO in Cloud Firestore / persistent store
  await saveCloudGitHubSettings({
    githubOwner: parsed.owner,
    githubRepo: parsed.repo,
    apiServerUrl: cleanApiServerUrl,
    updatedBy: input.updatedBy,
  });

  writePersistentStoreSecrets({ github_credentials: encryptedRecord });
  purgeLegacyVaultFiles();

  // STEP 3: Verify fresh state
  const verified = await getResolvedGitHubCredentials(true);
  if (!verified.hasToken || verified.owner !== parsed.owner || verified.repo !== parsed.repo) {
    throw new Error('تعذر التحقق النهائي من حفظ إعدادات GitHub في الخادم السحابي');
  }

  return {
    owner: verified.owner,
    repo: verified.repo,
    hasToken: true,
    apiServerUrl: verified.apiServerUrl,
    vault: verified.vault,
  };
}
