#!/bin/zsh

rm -rf ./archive && mkdir archive
git archive --format zip --prefix coq-hylos/ --worktree-attributes HEAD -o archive/coq-hylos.zip
