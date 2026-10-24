import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rmr_compresscard
open Finset StatMech StatMech.Walls


/--
[isDownAtCoord_iff_image_erase_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_compresscard.lean)
-/
@[path]
private lemma isDownAtCoord_iff_image_erase_closed_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (ConfigSpace E)} :
-- imply
  IsDownAtCoord i 𝒜 ↔ ∀ s ∈ 𝒜.image cfgSupport, s.erase i ∈ 𝒜.image cfgSupport := by
-- proof
  apply StatMech.Walls.isDownAtCoord_iff_image_erase_closed i 𝒜

/--
[rmr_downCompress_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_compresscard.lean)
-/
@[path]
private lemma rmr_downCompress_card_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (ConfigSpace E)} :
-- imply
  (downCompress i 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.Walls.rmr_downCompress_card i 𝒜

/--
[rmr_downCompress_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_compresscard.lean)
-/
@[path]
private lemma rmr_downCompress_idem_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (ConfigSpace E)} :
-- imply
  downCompress i (downCompress i 𝒜) = downCompress i 𝒜 := by
-- proof
  apply StatMech.Walls.rmr_downCompress_idem i 𝒜

/--
[rmr_downCompress_isDownAtCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_compresscard.lean)
-/
@[path]
private lemma rmr_downCompress_isDownAtCoord_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (ConfigSpace E)} :
-- imply
  IsDownAtCoord i (downCompress i 𝒜) := by
-- proof
  apply StatMech.Walls.rmr_downCompress_isDownAtCoord i 𝒜

/--
[rmr_compressCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_compresscard.lean)
-/
@[path]
private lemma rmr_compressCard_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (ConfigSpace E)} :
-- imply
  (downCompress i 𝒜).card = 𝒜.card ∧ downCompress i (downCompress i 𝒜) = downCompress i 𝒜 ∧ IsDownAtCoord i (downCompress i 𝒜) := by
-- proof
  apply StatMech.Walls.rmr_compressCard i 𝒜

/--
[rmr_downCompress_eq_self_of_isDownAtCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_compresscard.lean)
-/
@[path]
private lemma rmr_downCompress_eq_self_of_isDownAtCoord_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (ConfigSpace E)}
-- given
  (h : IsDownAtCoord i 𝒜) :
-- imply
  downCompress i 𝒜 = 𝒜 := by
-- proof
  apply StatMech.Walls.rmr_downCompress_eq_self_of_isDownAtCoord i 𝒜 h

/--
[rmr_isDownAtCoord_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_compresscard.lean)
-/
@[path]
private lemma rmr_isDownAtCoord_empty_eq
  [Fintype E]
  [DecidableEq E]
  {i : E} :
-- imply
  IsDownAtCoord i (∅ : Finset (ConfigSpace E)) := by
-- proof
  apply StatMech.Walls.rmr_isDownAtCoord_empty i

/--
[rmr_isDownAtCoord_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_compresscard.lean)
-/
@[path]
private lemma rmr_isDownAtCoord_univ_eq
  [Fintype E]
  [DecidableEq E]
  {i : E} :
-- imply
  IsDownAtCoord i (Finset.univ : Finset (ConfigSpace E)) := by
-- proof
  apply StatMech.Walls.rmr_isDownAtCoord_univ i


-- created on 2026-10-23
