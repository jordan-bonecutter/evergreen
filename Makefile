.DEFAULT_GOAL := help

NODE ?= node
PYTHON ?= python3
AWS_PROFILE ?= AdministratorAccess-388944274979
AWS_REGION ?= us-east-2
WEBSITE_DOMAIN ?= evergreenlang.net
WEBSITE_HOSTED_ZONE_ID ?= Z0305075324IKXGPI7RJN
WEBSITE_STACK_NAME ?= EvergreenWebsite
PORT ?= 4173

.PHONY: help website website-test website-serve login publish

help:
	@echo "make website        Build the website and Wasm compiler"
	@echo "make website-test   Build and test the browser compiler"
	@echo "make website-serve  Build and serve locally on port $(PORT)"
	@echo "make login          Renew the configured AWS SSO session"
	@echo "make publish        Build, test, and publish to $(WEBSITE_DOMAIN)"

website:
	"$(NODE)" web/build.mjs

website-test: website
	"$(NODE)" --test web/tests/compiler.test.mjs

website-serve: website
	"$(PYTHON)" -m http.server "$(PORT)" --directory web/dist --bind 127.0.0.1

login:
	aws sso login --profile "$(AWS_PROFILE)"

publish:
	"$(NODE)" web/deploy-aws.mjs \
		--profile "$(AWS_PROFILE)" --region "$(AWS_REGION)" \
		--stack-name "$(WEBSITE_STACK_NAME)" --domain "$(WEBSITE_DOMAIN)" \
		--hosted-zone-id "$(WEBSITE_HOSTED_ZONE_ID)"
