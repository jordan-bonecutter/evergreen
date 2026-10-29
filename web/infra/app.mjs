import { App, CfnOutput, Duration, RemovalPolicy, Stack } from 'aws-cdk-lib';
import * as s3 from 'aws-cdk-lib/aws-s3';
import * as cloudfront from 'aws-cdk-lib/aws-cloudfront';
import { S3BucketOrigin } from 'aws-cdk-lib/aws-cloudfront-origins';
import * as deployment from 'aws-cdk-lib/aws-s3-deployment';
import * as acm from 'aws-cdk-lib/aws-certificatemanager';
import * as route53 from 'aws-cdk-lib/aws-route53';
import { CloudFrontTarget } from 'aws-cdk-lib/aws-route53-targets';
import { fileURLToPath } from 'node:url';

const app = new App();
const domainName = process.env.EVERGREEN_DOMAIN_NAME;
const hostedZoneId = process.env.EVERGREEN_HOSTED_ZONE_ID;
if (Boolean(domainName) !== Boolean(hostedZoneId)) throw new Error('Set both domain name and hosted zone ID.');
const stackName = process.env.EVERGREEN_STACK_NAME || 'EvergreenWebsite';
const certificateStack = domainName ? new Stack(app, `${stackName}Certificate`, {
  description: 'Evergreen CloudFront HTTPS certificate (required in us-east-1)',
  env: { account: process.env.CDK_DEFAULT_ACCOUNT, region: 'us-east-1' },
  crossRegionReferences: true,
}) : undefined;
const stack = new Stack(app, process.env.EVERGREEN_STACK_NAME || 'EvergreenWebsite', {
  description: 'Evergreen static website: private S3 origin and HTTPS CloudFront CDN',
  env: {
    account: process.env.CDK_DEFAULT_ACCOUNT,
    region: process.env.CDK_DEFAULT_REGION,
  },
  crossRegionReferences: true,
});

const zone = domainName ? route53.HostedZone.fromHostedZoneAttributes(stack, 'DomainZone', {
  hostedZoneId,
  zoneName: domainName,
}) : undefined;
const certificateZone = domainName ? route53.HostedZone.fromHostedZoneAttributes(certificateStack, 'DomainZone', {
  hostedZoneId,
  zoneName: domainName,
}) : undefined;
const certificate = domainName ? new acm.Certificate(certificateStack, 'DomainCertificate', {
  domainName,
  validation: acm.CertificateValidation.fromDns(certificateZone),
}) : undefined;

const bucket = new s3.Bucket(stack, 'Website', {
  blockPublicAccess: s3.BlockPublicAccess.BLOCK_ALL,
  objectOwnership: s3.ObjectOwnership.BUCKET_OWNER_ENFORCED,
  encryption: s3.BucketEncryption.S3_MANAGED,
  enforceSSL: true,
  removalPolicy: RemovalPolicy.RETAIN,
});

// Stable filenames (including worker imports and the compiler) must revalidate.
const cache = new cloudfront.CachePolicy(stack, 'RevalidateCache', {
  minTtl: Duration.seconds(0),
  defaultTtl: Duration.seconds(0),
  maxTtl: Duration.days(1),
  enableAcceptEncodingGzip: true,
  enableAcceptEncodingBrotli: true,
});

const distribution = new cloudfront.Distribution(stack, 'Cdn', {
  domainNames: domainName ? [domainName] : undefined,
  certificate,
  minimumProtocolVersion: certificate ? cloudfront.SecurityPolicyProtocol.TLS_V1_2_2021 : undefined,
  defaultRootObject: 'index.html',
  priceClass: cloudfront.PriceClass.PRICE_CLASS_100,
  defaultBehavior: {
    origin: S3BucketOrigin.withOriginAccessControl(bucket),
    viewerProtocolPolicy: cloudfront.ViewerProtocolPolicy.REDIRECT_TO_HTTPS,
    allowedMethods: cloudfront.AllowedMethods.ALLOW_GET_HEAD_OPTIONS,
    cachePolicy: cache,
    compress: true,
    responseHeadersPolicy: cloudfront.ResponseHeadersPolicy.SECURITY_HEADERS,
  },
});

if (zone) {
  for (const [id, Record] of [['DomainIpv4', route53.ARecord], ['DomainIpv6', route53.AaaaRecord]]) {
    new Record(stack, id, {
      zone,
      target: route53.RecordTarget.fromAlias(new CloudFrontTarget(distribution)),
    });
  }
}

new deployment.BucketDeployment(stack, 'PublishWebsite', {
  sources: [deployment.Source.asset(fileURLToPath(new URL('../dist', import.meta.url)))],
  destinationBucket: bucket,
  distribution,
  distributionPaths: ['/*'],
  cacheControl: [deployment.CacheControl.fromString('public, max-age=0, must-revalidate')],
  // This dedicated bucket belongs to this stack; remove files from older builds.
  prune: true,
  retainOnDelete: true,
});

new CfnOutput(stack, 'WebsiteUrl', { value: `https://${domainName || distribution.distributionDomainName}` });
new CfnOutput(stack, 'CloudFrontUrl', { value: `https://${distribution.distributionDomainName}` });
new CfnOutput(stack, 'BucketName', { value: bucket.bucketName });
new CfnOutput(stack, 'DistributionId', { value: distribution.distributionId });
