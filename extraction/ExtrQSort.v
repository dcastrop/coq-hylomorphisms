Require Import HYLO.Extraction.
Require Import Examples.BTree.
Require Import Examples.QSort.

Extraction Inline posL.
Extraction Inline posR.
Set Extraction Flag 2047.
Extraction "qsort" qsort qsort_times_two.
