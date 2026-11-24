import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.InfluenceDerivative.booleanFourier.ne_flipCoord_iff_insertNth
open BooleanFourier Bool


/--
[influence_filter_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/InfluenceDerivative.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {f : (Fin (n + 1) → Bool) → Bool}
  {i : Fin (n + 1)} :
-- imply
  (Finset.univ.filter fun x : Fin (n + 1) → Bool => f x ≠ f (flipCoord x i)).card = 2 * (Finset.univ.filter fun y : Fin n → Bool => f (Fin.insertNth i true y) ≠ f (Fin.insertNth i false y)).card := by
-- proof
  rw [Finset.card_filter, Finset.card_filter]
  have h := Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => Bool) i).symm
    (fun x : Fin (n + 1) → Bool => if f x ≠ f (flipCoord x i) then 1 else 0)
    (fun p : Bool × (Fin n → Bool) =>
      if f (Fin.insertNth i p.1 p.2) ≠ f (flipCoord (Fin.insertNth i p.1 p.2) i) then 1 else 0)
    (by intro p; simp)
  rw [h]
  simp_rw [ne_flipCoord_iff_insertNth]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, ← two_mul]


lemma BooleanFourier.influence_filter_card_eq
  {n : ℕ}
  {f : (Fin (n + 1) → Bool) → Bool}
  {i : Fin (n + 1)} :
-- imply
  (Finset.univ.filter fun x : Fin (n + 1) → Bool => f x ≠ f (flipCoord x i)).card = 2 * (Finset.univ.filter fun y : Fin n → Bool => f (Fin.insertNth i true y) ≠ f (Fin.insertNth i false y)).card := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
