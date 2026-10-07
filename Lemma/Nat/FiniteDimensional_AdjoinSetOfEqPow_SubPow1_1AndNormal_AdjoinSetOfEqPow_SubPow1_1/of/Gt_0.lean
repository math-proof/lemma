import Mathlib
import sympy.Basic

open IntermediateField
open Polynomial

/--
[IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic.lean)
-/
@[main]
private lemma main
  {q : ℕ} [Fact q.Prime]
  {K : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] K]
  {N : ℕ}
-- given
  (hN : 0 < N) :
-- imply
  FiniteDimensional K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ∧ Normal K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := by
-- proof
  classical
  have hq : 1 < q := (Fact.out : q.Prime).one_lt
  have hm : 0 < q ^ N - 1 := by
    have : 1 < q ^ N := Nat.one_lt_pow hN.ne' hq
    omega

  set P : (↥K)[X] := X ^ (q ^ N - 1) - 1 with hP
  have hP0 : P ≠ 0 := by
    rw [hP]
    exact Polynomial.X_pow_sub_C_ne_zero hm 1
  have hset : {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} = P.rootSet (PadicAlgCl q) := by
    ext ζ
    rw [Polynomial.mem_rootSet, hP]
    simp only [Set.mem_ofPred_eq, map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
    exact ⟨fun h => ⟨hP0, h⟩, fun h => h.2⟩
  rw [hset]
  have : IsSplittingField K (IntermediateField.adjoin K (P.rootSet (PadicAlgCl q))) P :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  exact ⟨IsSplittingField.finiteDimensional _ P, Normal.of_isSplittingField P⟩


-- created on 2026-10-05
