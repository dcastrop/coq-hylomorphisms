Require Import HYLO.Extraction.
Require Import Examples.MSort.

Extract Inlined Constant Nat.leb => "(<=)".
Set Extraction Flag 2047.
Extraction "msort" msort.
