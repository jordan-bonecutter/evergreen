#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { parseArgs } from 'node:util';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

const root = path.dirname(fileURLToPath(import.meta.url));
const { values } = parseArgs({ options: {
  profile: { type: 'string' }, region: { type: 'string' },
  'stack-name': { type: 'string', default: 'EvergreenWebsite' },
  'skip-build': { type: 'boolean', default: false },
  domain: { type: 'string' }, 'hosted-zone-id': { type: 'string' },
  help: { type: 'boolean', short: 'h' },
} });
if (values.help) {
  console.log(`Usage: node web/deploy-aws.mjs [--profile NAME] [--region REGION]
       [--stack-name NAME] [--skip-build] [--domain DOMAIN --hosted-zone-id ID]

Builds and tests the site, installs locked CDK dependencies, bootstraps CDK in
your selected account/region, and deploys a PUBLIC HTTPS website on CloudFront
with a private S3 bucket. Uses your AWS CLI credentials (including AWS SSO).
CDK displays security-sensitive IAM changes for approval before deployment.
Requires Node 22+, npm, Rust with wasm32-unknown-unknown, and AWS CLI v2.`);
  process.exit(0);
}
if (!/^[A-Za-z][A-Za-z0-9-]{0,127}$/.test(values['stack-name'])) throw new Error('Invalid CloudFormation stack name.');
if (Boolean(values.domain) !== Boolean(values['hosted-zone-id'])) throw new Error('Use --domain and --hosted-zone-id together.');
if (values.domain && !/^(?:[a-z0-9](?:[a-z0-9-]*[a-z0-9])?\.)+[a-z]{2,}$/.test(values.domain)) throw new Error('Invalid domain name.');

const env = { ...process.env, AWS_PAGER: '' };
if (values.profile) env.AWS_PROFILE = values.profile;
function run(command, args, { capture = false, cwd = root } = {}) {
  const result = spawnSync(command, args, { env, cwd, encoding: 'utf8', stdio: capture ? ['ignore', 'pipe', 'inherit'] : 'inherit' });
  if (result.error) throw result.error;
  if (result.status !== 0) throw new Error(`${command} failed (exit ${result.status}).`);
  return result.stdout?.trim();
}
try {
  const region = values.region || env.AWS_REGION || env.AWS_DEFAULT_REGION
    || run('aws', ['configure', 'get', 'region'], { capture: true });
  if (!region) throw new Error('Choose an AWS region with --region or AWS_REGION.');
  env.AWS_REGION = env.AWS_DEFAULT_REGION = region;
  const { Account: account } = JSON.parse(run('aws', ['sts', 'get-caller-identity', '--output', 'json'], { capture: true }));
  if (!/^\d{12}$/.test(account)) throw new Error('AWS CLI returned an invalid account ID.');
  env.CDK_DEFAULT_ACCOUNT = account;
  env.CDK_DEFAULT_REGION = region;
  env.EVERGREEN_STACK_NAME = values['stack-name'];
  if (values.domain) {
    env.EVERGREEN_DOMAIN_NAME = values.domain;
    env.EVERGREEN_HOSTED_ZONE_ID = values['hosted-zone-id'];
  }
  console.log(`Deploying ${env.EVERGREEN_STACK_NAME} to AWS account ${account}, region ${region}.`);
  if (!values['skip-build']) run(process.execPath, ['build.mjs']);
  run(process.execPath, ['--test', 'tests/compiler.test.mjs']);
  const infra = path.join(root, 'infra');
  run('npm', ['ci', '--no-audit', '--no-fund'], { cwd: infra });
  const cdk = path.join(infra, 'node_modules/aws-cdk/bin/cdk');
  run(process.execPath, [cdk, 'bootstrap', `aws://${account}/${region}`], { cwd: infra });
  if (values.domain && region !== 'us-east-1') run(process.execPath, [cdk, 'bootstrap', `aws://${account}/us-east-1`], { cwd: infra });
  const stacks = values.domain ? [`${env.EVERGREEN_STACK_NAME}Certificate`, env.EVERGREEN_STACK_NAME] : [env.EVERGREEN_STACK_NAME];
  run(process.execPath, [cdk, 'diff', ...stacks], { cwd: infra });
  run(process.execPath, [cdk, 'deploy', ...stacks, '--require-approval', 'broadening'], { cwd: infra });
} catch (error) {
  console.error(error.message);
  process.exitCode = 1;
}
