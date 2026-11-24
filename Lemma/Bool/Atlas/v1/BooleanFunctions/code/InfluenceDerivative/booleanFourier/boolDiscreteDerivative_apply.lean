import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.InfluenceDerivative
open BooleanFourier


/--
[boolDiscreteDerivative_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/InfluenceDerivative.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {g : (Fin (n + 1) → Bool) → ℝ}
  {i : Fin (n + 1)}
  {y : Fin n → Bool} :
-- imply
  boolDiscreteDerivative g i y = (1 / 2 : ℝ) * (g (Fin.insertNth i true y) - g (Fin.insertNth i false y)) :=
-- proof
  rfl


lemma BooleanFourier.boolDiscreteDerivative_apply
  {n : ℕ}
  {g : (Fin (n + 1) → Bool) → ℝ}
  {i : Fin (n + 1)}
  {y : Fin n → Bool} :
-- imply
  boolDiscreteDerivative g i y = (1 / 2 : ℝ) * (g (Fin.insertNth i true y) - g (Fin.insertNth i false y)) := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
