import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc_itercompcard
open Finset StatMech StatMech.Walls


/--
[iterDownCompress_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_itercompcard.lean)
-/
@[path]
private lemma iterDownCompress_nil_eq
  [Fintype E]
  [DecidableEq E]
  {𝒜 : Finset (ConfigSpace E)} :
-- imply
  iterDownCompress [] 𝒜 = 𝒜 := by
-- proof
  apply StatMech.Walls.iterDownCompress_nil 𝒜

/--
[iterDownCompress_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_itercompcard.lean)
-/
@[path]
private lemma iterDownCompress_cons_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {cs : List E}
  {𝒜 : Finset (ConfigSpace E)} :
-- imply
  iterDownCompress (i :: cs) 𝒜 = downCompress i (iterDownCompress cs 𝒜) := by
-- proof
  apply StatMech.Walls.iterDownCompress_cons i cs 𝒜

/--
[rc_iterDownCompress_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_itercompcard.lean)
-/
@[path]
private lemma rc_iterDownCompress_card_eq
  [Fintype E]
  [DecidableEq E]
  {cs : List E}
  {𝒜 : Finset (ConfigSpace E)} :
-- imply
  (iterDownCompress cs 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.Walls.rc_iterDownCompress_card cs 𝒜

/--
[rc_iterDownCompress_eq_self_of_isDownAtCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_itercompcard.lean)
-/
@[path]
private lemma rc_iterDownCompress_eq_self_of_isDownAtCoord_eq
  [Fintype E]
  [DecidableEq E]
  {cs : List E}
  {𝒜 : Finset (ConfigSpace E)}
-- given
  (h : ∀ i ∈ cs, IsDownAtCoord i 𝒜) :
-- imply
  iterDownCompress cs 𝒜 = 𝒜 := by
-- proof
  apply StatMech.Walls.rc_iterDownCompress_eq_self_of_isDownAtCoord cs 𝒜 h

/--
[rc_iterDownCompress_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_itercompcard.lean)
-/
@[path]
private lemma rc_iterDownCompress_empty_eq
  [Fintype E]
  [DecidableEq E]
  {cs : List E} :
-- imply
  iterDownCompress cs (∅ : Finset (ConfigSpace E)) = ∅ := by
-- proof
  apply StatMech.Walls.rc_iterDownCompress_empty cs

/--
[rc_iterDownCompress_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_itercompcard.lean)
-/
@[path]
private lemma rc_iterDownCompress_univ_eq
  [Fintype E]
  [DecidableEq E]
  {cs : List E} :
-- imply
  iterDownCompress cs (Finset.univ : Finset (ConfigSpace E)) = Finset.univ := by
-- proof
  apply StatMech.Walls.rc_iterDownCompress_univ cs

/--
[rc_iterDownCompress_card_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_itercompcard.lean)
-/
@[path]
private lemma rc_iterDownCompress_card_univ_eq
  [Fintype E]
  [DecidableEq E]
  {cs : List E} :
-- imply
  (iterDownCompress cs (Finset.univ : Finset (ConfigSpace E))).card = 2 ^ Fintype.card E := by
-- proof
  apply StatMech.Walls.rc_iterDownCompress_card_univ cs


-- created on 2026-10-23
