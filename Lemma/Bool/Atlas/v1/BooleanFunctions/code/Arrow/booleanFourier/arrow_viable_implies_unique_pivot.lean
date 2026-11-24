import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Arrow.booleanFourier.exists_true_flip_witness
open BooleanFourier Bool


/--
[arrow_viable_implies_unique_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma main
  {n m : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i j : Fin n}
-- given
  (hm : m ≥ 3)
  (hviable : IsArrowViable f m)
  (hodd : IsOdd f)
  (hi : influence f i > 0)
  (hj : influence f j > 0) :
-- imply
  i = j := by
-- proof
  by_contra hne
  obtain ⟨x, hfx, hfxi⟩ := exists_true_flip_witness hi
  obtain ⟨y, hfy, hfyj⟩ := exists_true_flip_witness hj
  if hxi_yi : x i ≠ y i then
    have hw : ∀ k, x k = y k → flipCoord x i k = x k := by
      intro k hk
      have hki : k ≠ i := fun heq => by subst heq; exact hxi_yi hk
      simp [flipCoord, Function.update, hki]
    have hcontra := arrow_viable_subcube (f := f) (u := x) (v := y) (w := flipCoord x i) hm hviable hfx hfy hw
    rw [hfxi] at hcontra
    exact Bool.noConfusion hcontra
  else
    have hxi_yi : x i = y i := not_ne_iff.mp hxi_yi
    if hxj_yj : x j ≠ y j then
      have hw : ∀ k, x k = y k → flipCoord y j k = x k := by
        intro k hk
        have hkj : k ≠ j := fun heq => by subst heq; exact hxj_yj hk
        simp [flipCoord, Function.update, hkj]
        exact hk.symm
      have hcontra := arrow_viable_subcube (f := f) (u := x) (v := y) (w := flipCoord y j) hm hviable hfx hfy hw
      rw [hfyj] at hcontra
      exact Bool.noConfusion hcontra
    else
      have hxj_yj : x j = y j := not_ne_iff.mp hxj_yj
      let z : Fin n → Bool := fun k => !(flipCoord y j k)
      have hfz : f z = true := by
        have h := hodd (flipCoord y j)
        show f (fun k => !(flipCoord y j k)) = true
        rw [h, hfyj, Bool.not_false]
      have hxi_ne_zi : x i ≠ z i := by
        show x i ≠ !(flipCoord y j i)
        simp only [flipCoord, Function.update, dite_eq_right hne]
        rw [hxi_yi]
        exact Bool.self_ne_not (y i)
      have hw : ∀ k, x k = z k → flipCoord x i k = x k := by
        intro k hk
        have hki : k ≠ i := fun heq => by subst heq; exact hxi_ne_zi hk
        simp [flipCoord, Function.update, hki]
      have hcontra := arrow_viable_subcube (f := f) (u := x) (v := z) (w := flipCoord x i) hm hviable hfx hfz hw
      rw [hfxi] at hcontra
      exact Bool.noConfusion hcontra


lemma BooleanFourier.arrow_viable_implies_unique_pivot
  {n m : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i j : Fin n}
-- given
  (hm : m ≥ 3)
  (hviable : IsArrowViable f m)
  (hodd : IsOdd f)
  (hi : influence f i > 0)
  (hj : influence f j > 0) :
-- imply
  i = j :=
-- proof
  main hm hviable hodd hi hj


-- created on 2026-10-23
-- updated on 2026-11-24
