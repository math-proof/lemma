import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.SharpThreshold
open BooleanFourier Finset


/--
[influence_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/SharpThreshold.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n} :
-- imply
  influence f i ≤ 1 := by
-- proof
  unfold influence
  rw [div_le_one (by positivity : (2 : ℝ) ^ n > 0)]
  have hle : (Finset.univ.filter fun x => f x ≠ f (flipCoord x i)).card ≤
    Finset.univ.card :=
    Finset.card_filter_le _ _
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hle
  exact_mod_cast hle


lemma BooleanFourier.influence_le_one
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n} :
-- imply
  influence f i ≤ 1 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
