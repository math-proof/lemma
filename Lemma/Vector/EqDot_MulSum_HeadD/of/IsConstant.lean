import Lemma.Algebra.SumCons.eq.Add_Sum
import Lemma.Vector.SumMap_FunMul.eq.DotMapS
import Lemma.Algebra.EqMap_Id
import Lemma.Vector.Map.eq.Replicate
import Lemma.Vector.Eq_Replicate_HeadD.of.IsConstant
import Lemma.Vector.SumMap_FunMul.eq.MulSumMap
open Algebra Vector


@[main]
private lemma main
  [Add α] [MulZeroClass α] [RightDistribClass α]
  {s s' : List.Vector α n}
-- given
  (h: s is constant)
  (default : α) :
-- imply
  s' ⬝ s = s'.sum * s.headD default := by
-- proof
  have h_eq_sum := SumMap_FunMul.eq.DotMapS
    (s := s')
    (f₁ := id)
    (f₂ := fun _ => s.headD default)
  have h_eq := Eq_Replicate_HeadD.of.IsConstant h default (s := s)
  simp at h_eq_sum
  rw [
    Map.eq.Replicate,
    h_eq.symm
  ] at h_eq_sum
  have h_eq := SumMap_FunMul.eq.MulSumMap
    (s := s')
    (f := id)
    (const := s.headD default)
  simp at h_eq
  rw [h_eq_sum.symm, h_eq]


-- created on 2024-07-01
