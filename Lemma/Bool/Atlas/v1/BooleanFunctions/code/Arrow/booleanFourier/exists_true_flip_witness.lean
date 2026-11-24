import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Arrow.booleanFourier.arrow_viable_subcube
open BooleanFourier Bool


/--
[exists_true_flip_witness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n}
-- given
  (hi : influence f i > 0) :
-- imply
  ∃ x : Fin n → Bool, f x = true ∧ f (flipCoord x i) = false := by
-- proof
  unfold influence at hi
  have hcard : 0 < (Finset.univ.filter fun x => f x ≠ f (flipCoord x i)).card := by
    by_contra h
    have h' : (Finset.univ.filter fun x => f x ≠ f (flipCoord x i)).card = 0 := by omega
    simp [h'] at hi
  rw [Finset.card_pos] at hcard
  obtain ⟨x, hx⟩ := hcard
  have hx' := (Finset.mem_filter.mp hx).2
  cases hfx : f x with
  | false =>
    cases hfx' : f (flipCoord x i) with
    | false => simp [hfx, hfx'] at hx'
    | true =>
      refine ⟨flipCoord x i, hfx', ?_⟩
      have heq : flipCoord (flipCoord x i) i = x := by
        funext k
        if hk : k = i then
          subst hk
          simp [flipCoord, Bool.not_not]
        else
          simp [flipCoord, Function.update, hk]
      rw [heq, hfx]
  | true =>
    cases hfx' : f (flipCoord x i) with
    | false => exact ⟨x, hfx, hfx'⟩
    | true => simp [hfx, hfx'] at hx'


lemma BooleanFourier.exists_true_flip_witness
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n}
-- given
  (hi : influence f i > 0) :
-- imply
  ∃ x : Fin n → Bool, f x = true ∧ f (flipCoord x i) = false :=
-- proof
  main hi


-- created on 2026-10-23
-- updated on 2026-11-24
