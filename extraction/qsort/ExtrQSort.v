Require Import Hylo.Extraction.Common.
Require Import Hylo.Examples.BTree.
Require Import Hylo.Examples.QSort.

Extraction Inline posL.
Extraction Inline posR.
Set Extraction Flag 2047.
Extraction "qsort" qsort qsort_times_two.
