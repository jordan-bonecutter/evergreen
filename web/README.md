# Evergreen website

Static landing page and a browser playground. No runtime npm dependencies or server API.

```sh
rustup target add wasm32-unknown-unknown
node web/build.mjs
node --test web/tests/compiler.test.mjs
python3 -m http.server 4173 --directory web/dist
```

Open http://localhost:4173. Node 22+ and Rust are required for development.
The build compiles `web/compiler` to Wasm and copies the site and root `logo.svg`
into ignored `web/dist`. The SVG page bounds are cropped without changing the artwork.

The compiler runs in a module Worker. Each run creates a fresh compiler instance,
checks the source with Evergreen's verifier, emits an executable Wasm module,
then instantiates it with the console host in `public/runtime.js`. Source stays
in the browser; drafts use localStorage when available. No user code is evaluated
as JavaScript. The page reports trusted assumptions explicitly.

The browser limits source and console output to 100 KB each and terminates work
after 20 seconds. Stop terminates and replaces the Worker. Failed proofs never
produce a runnable module. Download saves the last compiled module for the current
source. See [WebAssembly target notes](../docs/wasm.md) for the ABI and supported subset.

Sites hosting configuration is in `.openai/hosting.json`; serve `dist` as static assets.
Rebuild before publishing so the compiler and examples stay in sync.

## Deploy to AWS

The CDK stack in `infra/` uses a private S3 bucket and a public CloudFront HTTPS
distribution with Origin Access Control. It uploads only `dist`, compresses
responses, and invalidates CloudFront after uploads. The default CloudFront
domain includes HTTPS; no custom domain, DNS zone, or certificate setup is needed.

Install Node 22+ (with npm), Rust with the Wasm target, and AWS CLI v2. Configure
your AWS CLI profile first, using `aws configure` or `aws configure sso` and
`aws sso login --profile your-profile` as appropriate. Then, from the repo root:

```sh
node web/deploy-aws.mjs --profile your-profile --region us-east-1
```

Omit `--profile` to use the default AWS credential chain. `AWS_PROFILE` and
`AWS_REGION` / `AWS_DEFAULT_REGION` are supported. The script checks the selected
account, builds and tests the site, installs locked CDK dependencies, bootstraps
CDK in that account/region, and deploys the `EvergreenWebsite` stack. CDK presents
IAM permission changes for approval. It prints `WebsiteUrl`, `BucketName`, and
`DistributionId` after deployment. Rerun the same command to publish updates.
Use `--stack-name AnotherName` for an independent site or `--skip-build` to use
an existing `dist` (tests still run). CloudFront deployment can take several minutes.

The selected identity needs permissions to bootstrap CDK and deploy CloudFormation,
S3, CloudFront, Lambda, and IAM resources. BucketDeployment uses a CDK-managed
Lambda to upload assets and invalidate the cache; the website itself has no server.
AWS storage, requests, data transfer, and deployment resources can incur charges.
Deleting the stack retains the website bucket and its contents; CDK bootstrap
resources also remain. Cleanup of retained buckets is manual and separate.

To inspect the generated infrastructure without deploying (after building):

```sh
cd web/infra
npm ci
npm run synth -- --no-lookups
```

No credentials or secrets are embedded in the site or committed by this setup.

### evergreenlang.net

Deploy the registered domain using its existing public Route 53 hosted zone:

```sh
node web/deploy-aws.mjs --profile AdministratorAccess-388944274979 \
  --region us-east-2 --domain evergreenlang.net \
  --hosted-zone-id Z0305075324IKXGPI7RJN
```

This adds an ACM certificate with automatic DNS validation and apex A/AAAA alias
records. The website bucket and deployment resources use the selected region;
a separate `EvergreenWebsiteCertificate` stack uses `us-east-1` because CloudFront
requires its ACM certificate there. The script bootstraps both regions and deploys
the stacks in dependency order. Keep these domain flags on subsequent deployments so CDK
retains the certificate, aliases, and DNS records. Existing NS, SOA, mail, and
unrelated DNS records are preserved. The domain's registered nameservers must
point to this hosted zone; certificate issuance and DNS propagation can take time.
