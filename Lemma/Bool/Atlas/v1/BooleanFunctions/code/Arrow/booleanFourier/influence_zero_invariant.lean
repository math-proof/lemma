import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Arrow.booleanFourier.flipCoord_eq_of_ne
open BooleanFourier Bool


/--
[influence_zero_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {j : Fin n}
-- given
  (hj : influence f j = 0) :
-- imply
  ∀ x : Fin n → Bool, f x = f (flipCoord x j) := by
-- proof
  intro x
  unfold influence at hj
  have h2n : (2 : ℝ) ^ n > 0 := pow_pos (by norm_num : (2 : ℝ) > 0) n
  have hcard_nat : (Finset.univ.filter fun x => f x ≠ f (flipCoord x j)).card = 0 := by
    have : ((Finset.univ.filter fun x => f x ≠ f (flipCoord x j)).card : ℝ) = 0 :=
      (div_eq_zero_iff.mp hj).resolve_right (ne_of_gt h2n)
    exact_mod_cast this
  by_contra hne
  have hmem : x ∈ (Finset.univ.filter fun x => f x ≠ f (flipCoord x j)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
  rw [Finset.card_eq_zero.mp hcard_nat] at hmem; simp at hmem


lemma BooleanFourier.influence_zero_invariant
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {j : Fin n}
-- given
  (hj : influence f j = 0) :
-- imply
  ∀ x : Fin n → Bool, f x = f (flipCoord x j) :=
-- proof
  main hj


-- created on 2026-10-23
-- updated on 2026-11-24
