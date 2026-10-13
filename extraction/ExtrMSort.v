Require Import HYLO.Extraction.Common.
Require Import HYLO.Examples.MSort.

Extract Inlined Constant Nat.leb => "(<=)".
Set Extraction Flag 2047.
Extraction "msort" msort.
