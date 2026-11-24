module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion.booleanFourier.chi_flipAt
open Finset BigOperators BooleanFourier Bool


public section

/--
[sum_chi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {S : Finset (Fin n)} :
-- imply
  ∑ x : Fin n → Bool, chi S x = if S = ∅ then (2 : ℝ) ^ n else 0 := by
-- proof
  split_ifs with h
  ·
    subst h
    simp [chi, Fintype.card_bool]
  ·
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr h
    apply Finset.sum_ninvolution (g := fun x => flipAt j x)
    ·
      intro x
      have := chi_flipAt (S := S) (j := j) (x := x) hj
      linarith
    ·
      intro x _
      exact flipAt_ne_self (j := j) (x := x)
    ·
      intro x
      exact Finset.mem_univ _
    ·
      intro x
      exact flipAt_flipAt (j := j) (x := x)


theorem BooleanFourier.sum_chi
  {n : ℕ}
  {S : Finset (Fin n)} :
-- imply
  ∑ x : Fin n → Bool, chi S x = if S = ∅ then (2 : ℝ) ^ n else 0 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
