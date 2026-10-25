import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc5_itercompcard
open Finset StatMech StatMech.Walls


/--
[rc5_downComp_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_itercompcard.lean)
-/
@[path]
private lemma rc5_downComp_card_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  (Down.compression i 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.Walls.rc5_downComp_card i 𝒜

/--
[rc5_iterDownComp_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_itercompcard.lean)
-/
@[path]
private lemma rc5_iterDownComp_card_eq
  [DecidableEq α]
  {cs : List α}
  {𝒜 : Finset (Finset α)} :
-- imply
  (iterDownComp cs 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.Walls.rc5_iterDownComp_card cs 𝒜

/--
[rc5_iterDownComp_eq_self_of_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_itercompcard.lean)
-/
@[path]
private lemma rc5_iterDownComp_eq_self_of_isLowerSet_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {cs : List α}
-- given
  (h : IsLowerSet (𝒜 : Set (Finset α))) :
-- imply
  iterDownComp cs 𝒜 = 𝒜 := by
-- proof
  apply StatMech.Walls.rc5_iterDownComp_eq_self_of_isLowerSet h cs

/--
[rc5_iterDownComp_card_of_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_itercompcard.lean)
-/
@[path]
private lemma rc5_iterDownComp_card_of_isLowerSet_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {cs : List α}
-- given
  (h : IsLowerSet (𝒜 : Set (Finset α))) :
-- imply
  (iterDownComp cs 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.Walls.rc5_iterDownComp_card_of_isLowerSet h cs

/--
[rc5_iterDownComp_count_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_itercompcard.lean)
-/
@[path]
private lemma rc5_iterDownComp_count_mono_eq
  [DecidableEq α]
  {cs : List α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ) ∧ (iterDownComp cs 𝒜).card = 𝒜.card ∧ (iterDownComp cs ℬ).card = ℬ.card := by
-- proof
  apply StatMech.Walls.rc5_iterDownComp_count_mono cs 𝒜 ℬ

/--
[rc5_iterDownComp_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_itercompcard.lean)
-/
@[path]
private lemma rc5_iterDownComp_empty_eq
  [DecidableEq α]
  {cs : List α} :
-- imply
  iterDownComp cs (∅ : Finset (Finset α)) = ∅ := by
-- proof
  apply StatMech.Walls.rc5_iterDownComp_empty cs

/--
[rc5_iterDownComp_card_powerset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_itercompcard.lean)
-/
@[path]
private lemma rc5_iterDownComp_card_powerset_eq
  [DecidableEq α]
  {cs : List α}
  {s : Finset α} :
-- imply
  (iterDownComp cs s.powerset).card = 2 ^ s.card := by
-- proof
  apply StatMech.Walls.rc5_iterDownComp_card_powerset cs s

/--
[rc5_itercomp_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_itercompcard.lean)
-/
@[path]
private lemma rc5_itercomp_card_eq
  [DecidableEq α]
  {cs : List α}
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  (Down.compression i 𝒜).card = 𝒜.card ∧ (iterDownComp cs 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.Walls.rc5_itercomp_card cs i 𝒜


-- created on 2026-10-23
