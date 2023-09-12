From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.

Extract Inlined Constant Nat.leb => "(<=)".
Set Extraction TypeExpand.
(* Set Extraction Conservative Types. *)
Extraction Inline projT1.
Extraction Inline projT2.


Require Import HYLO.hylo.
Extraction Inline app.
Extraction Inline coalg.
Extraction Inline hylo.
Extraction Inline hylo_f.
Extraction Inline hylo_f_.

Extraction Inline merge.
Extraction Inline a_leaf.
Extraction Inline a_node.
Extraction Inline m_merge.
Extraction Inline m_split.
Extraction Inline a_out.
Extraction Inline c_split.
Extraction Inline tsplit.
Set Extraction Flag 2047.
Extraction "./extraction/test.ml" qsort.
