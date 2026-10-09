import sympy.core.mul
import sympy.Basic
import Lemma.Tensor.WrapFlat.eq.WrapFlatMod.of.EqLengthS
open Tensor


@[path]
private lemma main
  {i : ℕ}
-- given
  (s : List ℕ)
  (hi : i < s.prod) :
-- imply
  wrapFlat s s i = i := by
-- proof
  induction s generalizing i with
  | nil =>
    simp [wrapFlat] at hi ⊢
    omega
  | cons n s ih =>
    simp only [wrapFlat, List.prod_cons] at hi ⊢
    have hs : s.prod ≠ 0 := by
      intro hz
      simp [hz] at hi
    have hdiv : i / s.prod < n := by
      rw [Nat.mul_comm] at hi
      exact Nat.div_lt_of_lt_mul hi
    have hmod : i % s.prod < s.prod := Nat.mod_lt _ (Nat.pos_of_ne_zero hs)
    rw [Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt hdiv]
    rw [WrapFlat.eq.WrapFlatMod.of.EqLengthS s s rfl i, ih hmod, Nat.mul_comm, Nat.div_add_mod]


-- created on 2026-10-07
