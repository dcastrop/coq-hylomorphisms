#!/bin/zsh

rm -rf ./archive && mkdir archive
git archive --format zip --prefix rocq-hylos/ --worktree-attributes HEAD -o archive/rocq-hylos.zip
