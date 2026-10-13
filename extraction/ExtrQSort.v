Require Import HYLO.Container.
Require Import Examples.BTree.
Require Import Examples.QSort.

From Stdlib Require Extraction ExtrOcamlBasic ExtrOCamlInt63.
Set Extraction TypeExpand.
Extraction Inline val.
Extraction Inline posL.
Extraction Inline posR.
Set Extraction Flag 2047.
Extraction "qsort" qsort qsort_times_two.
