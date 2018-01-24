#!/bin/bash

curl -H "Authorization: token $(DOC_BOT_TOKEN)" \
  -H "Accept: application/vnd.github.manifold-preview" \
  -H "Content-Type: application/zip" \
  --data-binary @$1 \
  "https://uploads.github.com/repos/$(CIRCLE_PROJECT_USERNAME)/$(CIRCLE_PROJECT_REPONAME)/releases/$(CIRCLE_TAG)/assets?name=$2"
