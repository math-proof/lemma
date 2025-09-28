import stdlib.Slice
import sympy.sets.sets
import Lemma.Set.InAdd_Mul_DivSub1Sign_2.of.In_IcoNeg
import Lemma.Algebra.EqToNat.of.Ge_0
open Set Algebra


@[main]
private lemma main
  {i : ℤ}
  {n : ℕ}
-- given
  (h : i ∈ Ico (-n : ℤ) n) :
-- imply
  (Slice.Add_Mul_DivSub1Sign_2 n i).toNat < n := by
-- proof
  have h := InAdd_Mul_DivSub1Sign_2.of.In_IcoNeg h
  let ⟨h_le, h_lt⟩ := h
  have := EqToNat.of.Ge_0 h_le
  simp_all


-- created on 2025-06-26
