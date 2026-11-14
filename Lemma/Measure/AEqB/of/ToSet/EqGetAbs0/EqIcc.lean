import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval
@[path]
private lemma main
  {I : BoundedInterval}
-- given
  (hI : I = Icc I.a I.b)
  (h_len : |I|ₗ = 0)
  (h_nonempty : I.toSet.Nonempty) :
-- imply
  I.a = I.b :=
-- proof
  eq_of_length_zero_of_Icc hI h_len h_nonempty


-- created on 2026-10-22
