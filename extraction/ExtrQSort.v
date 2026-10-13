Require Import HYLO.Extraction.Common.
Require Import HYLO.Examples.BTree.
Require Import HYLO.Examples.QSort.

Extraction Inline posL.
Extraction Inline posR.
Set Extraction Flag 2047.
Extraction "qsort" qsort qsort_times_two.
