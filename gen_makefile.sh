#!/bin/sh

coq_makefile -f _CoqProject -o Makefile

[ ! -d extraction ] && mkdir extraction

exit 0
