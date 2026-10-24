import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc8tworowbands
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc8_mem_descentBand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_mem_descentBand_eq
  {r x : Site 2} :
-- imply
  x ∈ jc8_descentBand r ↔ x 1 ≤ r 1 - 2 := by
-- proof
  apply StatMech.Walls.jc8_mem_descentBand r x

/--
[jc8_mem_touchingBand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_mem_touchingBand_eq
  {r x : Site 2} :
-- imply
  x ∈ jc8_touchingBand r ↔ r 1 - 1 ≤ x 1 := by
-- proof
  apply StatMech.Walls.jc8_mem_touchingBand r x

/--
[jc8_descentBand_below_shelf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_descentBand_below_shelf_eq
  {r x : Site 2}
-- given
  (hx : x ∈ jc8_descentBand r) :
-- imply
  x 1 < jc8_shelfRow r := by
-- proof
  apply StatMech.Walls.jc8_descentBand_below_shelf r x hx

/--
[jc8_touchingBand_above_shelf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_touchingBand_above_shelf_eq
  {r x : Site 2}
-- given
  (hx : x ∈ jc8_touchingBand r) :
-- imply
  jc8_shelfRow r ≤ x 1 := by
-- proof
  apply StatMech.Walls.jc8_touchingBand_above_shelf r x hx

/--
[jc8_band_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_band_separation_eq
  {r u v : Site 2}
-- given
  (hu : u 1 ≤ r 1 - 2)
  (hv : r 1 - 1 ≤ v 1) :
-- imply
  u 1 < v 1 := by
-- proof
  apply StatMech.Walls.jc8_band_separation r u v hu hv

/--
[jc8_band_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_band_ne_eq
  {r u v : Site 2}
-- given
  (hu : u 1 ≤ r 1 - 2)
  (hv : r 1 - 1 ≤ v 1) :
-- imply
  u ≠ v := by
-- proof
  apply StatMech.Walls.jc8_band_ne r u v hu hv

/--
[jc8_bands_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_bands_disjoint_eq
  {r : Site 2} :
-- imply
  Disjoint (jc8_descentBand r) (jc8_touchingBand r) := by
-- proof
  apply StatMech.Walls.jc8_bands_disjoint r

/--
[jc8_band_separation_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_band_separation_mem_eq
  {r u v : Site 2}
-- given
  (hu : u ∈ jc8_descentBand r)
  (hv : v ∈ jc8_touchingBand r) :
-- imply
  u 1 < v 1 ∧ u ≠ v := by
-- proof
  apply StatMech.Walls.jc8_band_separation_mem r u v hu hv

/--
[jc8_descentFace_below_touchingFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_descentFace_below_touchingFace_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {i j : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hlow : jc8_DescentStaysLow K hK e he r i)
  (hband : jc8_TouchingFaceBand K hK e he r j)
  (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
-- imply
  (olb_orbitLoop K hK e he).getVert i 1 < (olb_orbitLoop K hK e he).getVert j 1 := by
-- proof
  apply StatMech.Walls.jc8_descentFace_below_touchingFace K hK e he r i j hlow hband htouch

/--
[jc8_descentFace_ne_touchingFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_descentFace_ne_touchingFace_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {i j : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hlow : jc8_DescentStaysLow K hK e he r i)
  (hband : jc8_TouchingFaceBand K hK e he r j)
  (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
-- imply
  (olb_orbitLoop K hK e he).getVert i ≠ (olb_orbitLoop K hK e he).getVert j := by
-- proof
  apply StatMech.Walls.jc8_descentFace_ne_touchingFace K hK e he r i j hlow hband htouch

/--
[jc8_twoRowBands](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_twoRowBands_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {i j : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hlow : jc8_DescentStaysLow K hK e he r i)
  (hband : jc8_TouchingFaceBand K hK e he r j)
  (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
-- imply
  (olb_orbitLoop K hK e he).getVert i ∈ jc8_descentBand r ∧ (olb_orbitLoop K hK e he).getVert j ∈ jc8_touchingBand r ∧ (olb_orbitLoop K hK e he).getVert i 1 < (olb_orbitLoop K hK e he).getVert j 1 ∧ (olb_orbitLoop K hK e he).getVert i ≠ (olb_orbitLoop K hK e he).getVert j := by
-- proof
  apply StatMech.Walls.jc8_twoRowBands K hK e he r i j hlow hband htouch

/--
[jc8_touchingFaceBand_of_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_touchingFaceBand_of_free_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {j : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hfree : jc4_FootprintFree K ⟨e, he⟩ r j) :
-- imply
  jc8_TouchingFaceBand K hK e he r j := by
-- proof
  apply StatMech.Walls.jc8_touchingFaceBand_of_free K hK e he r j hfree

/--
[jc8_descentStaysLow_of_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_descentStaysLow_of_row_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {i : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hrow : (olb_orbitLoop K hK e he).getVert i 1 ≤ r 1 - 2) :
-- imply
  jc8_DescentStaysLow K hK e he r i := by
-- proof
  apply StatMech.Walls.jc8_descentStaysLow_of_row K hK e he r i hrow

/--
[jc8_separation_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_separation_nonvacuous_eq :
-- imply
  ((![0, 0] : Site 2)) 1 < ((![0, 3] : Site 2)) 1 ∧ ((![0, 0] : Site 2)) ≠ ((![0, 3] : Site 2)) := by
-- proof
  apply StatMech.Walls.jc8_separation_nonvacuous

/--
[jc8_shelfRow_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_shelfRow_eq_eq
  {r : Site 2} :
-- imply
  jc8_shelfRow r = r 1 - 1 := by
-- proof
  apply StatMech.Walls.jc8_shelfRow_eq r

/--
[jc8_shelfRow_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean)
-/
@[path]
private lemma jc8_shelfRow_separates_eq
  {r : Site 2} :
-- imply
  r 1 - 2 < jc8_shelfRow r ∧ jc8_shelfRow r = r 1 - 1 := by
-- proof
  apply StatMech.Walls.jc8_shelfRow_separates r


-- created on 2026-10-23
