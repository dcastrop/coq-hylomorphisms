Require Import HYLO.Container.
Require Import Examples.MSort.

From Stdlib Require Extraction ExtrOcamlBasic ExtrOCamlInt63.
Extract Inlined Constant Nat.leb => "(<=)".
Set Extraction TypeExpand.
Extraction Inline val.
Set Extraction Flag 2047.
Extraction "msort" msort.
