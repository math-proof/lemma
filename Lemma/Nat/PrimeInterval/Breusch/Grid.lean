import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeInterval.Breusch.Grid
open MathlibExt.NumberTheory.BreuschWanted.Internal


/--
[M9_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
private lemma M9_le_eq
  :
-- imply
  ∀ j < 18900, G9 j ≤ 3 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.M9_le

/--
[jmin1_attained](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
private lemma jmin1_attained_eq
  :
-- imply
  G9 279 ≥ 1 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.jmin1_attained

/--
[jmin1_core](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
private lemma jmin1_core_eq
  :
-- imply
  ∀ j < 279, 10 ≤ j → G9 j < 1 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.jmin1_core

/--
[jmin1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
private lemma jmin1_eq
  :
-- imply
  G9 279 ≥ 1 ∧ ∀ j, 10 ≤ j → j < 279 → G9 j < 1 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.jmin1

/--
[jmin2_attained](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
private lemma jmin2_attained_eq
  :
-- imply
  G9 657 ≥ 2 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.jmin2_attained

/--
[jmin2_core](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
private lemma jmin2_core_eq
  :
-- imply
  ∀ j < 657, 10 ≤ j → G9 j < 2 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.jmin2_core

/--
[jmin2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
private lemma jmin2_eq
  :
-- imply
  G9 657 ≥ 2 ∧ ∀ j, 10 ≤ j → j < 657 → G9 j < 2 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.jmin2

/--
[jmin3_attained](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
private lemma jmin3_attained_eq
  :
-- imply
  G9 963 ≥ 3 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.jmin3_attained

/--
[jmin3_core](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
private lemma jmin3_core_eq
  :
-- imply
  ∀ j < 963, 10 ≤ j → G9 j < 3 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.jmin3_core

/--
[jmin3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
private lemma jmin3_eq
  :
-- imply
  G9 963 ≥ 3 ∧ ∀ j, 10 ≤ j → j < 963 → G9 j < 3 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.jmin3


-- created on 2026-10-20
