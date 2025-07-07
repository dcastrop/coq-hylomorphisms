#!/bin/zsh

rm -rf ./archive && mkdir archive
git archive --format zip --worktree-attributes HEAD -o archive/coq-hylos.zip
