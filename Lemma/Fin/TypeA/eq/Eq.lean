import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.SevenFamilies.Part3
open CoxeterMatrix


/--
[typeA_matrix_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SevenFamilies.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {i j : Fin n} :
-- imply
  typeA n i j = if i = j then 1 else if (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ) then 3 else 2 := by
-- proof
  simp [typeA, CoxeterMatrix.A, Matrix.of_apply]


/--
[affinBCond_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SevenFamilies.lean)
-/
private lemma affinBCond_comm_eq
  {i j : ℕ} :
-- imply
  affinBCond i j ↔ affinBCond j i := by
-- proof
  apply affinBCond_comm i j

/--
[affinDCond_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SevenFamilies.lean)
-/
private lemma affinDCond_comm_eq
  {n i j : ℕ} :
-- imply
  affinDCond n i j ↔ affinDCond n j i := by
-- proof
  apply affinDCond_comm n i j


-- created on 2026-10-23
-- updated on 2026-10-26
