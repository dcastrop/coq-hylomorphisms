Require Import Hylo.Morphism.
Require Import Hylo.Container.
Require Import Hylo.Algebra.
Require Import Hylo.Coalgebra.
Require Import Hylo.Extraction.Common.
Require Import Hylo.Examples.MutualRec.

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
Extraction "mutualrec" ToExtract.
