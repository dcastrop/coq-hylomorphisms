Require Import Hylo.Extraction.Common.
Require Import Hylo.Examples.MSort.

Extract Inlined Constant Nat.leb => "(<=)".
Set Extraction Flag 2047.
Extraction "msort" msort.
