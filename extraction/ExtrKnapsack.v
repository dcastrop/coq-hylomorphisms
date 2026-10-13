Require Import HYLO.Morphism.
Require Import HYLO.Container.
Require Import HYLO.Algebra.
Require Import HYLO.Coalgebra.
Require Import HYLO.Extraction.
Require Import Examples.Knapsack.

From Stdlib Require ExtrOcamlNatInt.
Extraction Inline LFix_out.
Extraction Inline shape.
Extraction Inline headT_.
Extraction Inline tailT_.
Extraction Inline l_out.
Extraction Inline Memo.
Extraction Inline fst.
Extraction Inline snd.
Extraction Inline pair.
Extraction Inline Morphism.app.
Extraction Inline Nat.pred.
Set Extraction Flag 2047.
Extraction "knapsack" ToExtract.
