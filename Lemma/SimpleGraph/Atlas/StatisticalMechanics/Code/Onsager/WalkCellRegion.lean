import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.WalkCellRegion
open StatMech StatMech.Onsager StatMech.Onsager.WalkCellRegion


/--
[cellFace_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma cellFace_zero_eq
  {p : ℤ × ℤ} :
-- imply
  cellFace p 0 = p.1 := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.cellFace_zero p

/--
[cellFace_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma cellFace_one_eq
  {p : ℤ × ℤ} :
-- imply
  cellFace p 1 = p.2 := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.cellFace_one p

/--
[cellFace_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma cellFace_symm_eq
  {z : Site 2} :
-- imply
  cellFace.symm z = (z 0, z 1) := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.cellFace_symm z

/--
[walkEdge_mem_imageGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma walkEdge_mem_imageGraph_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {k : Fin (m + 3)}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d)) :
-- imply
  s(posSite d k, posSite d (k + 1)) ∈ (imageGraph (walkP d hclosed hsimple)).edgeSet := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.walkEdge_mem_imageGraph d hclosed hsimple k

/--
[imageGraph_adj_pos_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma imageGraph_adj_pos_iff_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {k : Fin (m + 3)}
  {q : Site 2}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d)) :
-- imply
  (imageGraph (walkP d hclosed hsimple)).Adj (posSite d k) q ↔ q = posSite d (k - 1) ∨ q = posSite d (k + 1) := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.imageGraph_adj_pos_iff d hclosed hsimple k q

/--
[rayParity_eq_of_faceAdj_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma rayParity_eq_of_faceAdj_right_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {a b : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hadj : (walkRegionGraph d hclosed hsimple).Adj (cellFace (a, b)) (cellFace (a + 1, b))) :
-- imply
  rayParity d a b = rayParity d (a + 1) b := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.rayParity_eq_of_faceAdj_right d hclosed hsimple a b hadj

/--
[rayParity_eq_of_faceAdj_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma rayParity_eq_of_faceAdj_top_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {a b : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hadj : (walkRegionGraph d hclosed hsimple).Adj (cellFace (a, b)) (cellFace (a, b + 1))) :
-- imply
  rayParity d a b = rayParity d a (b + 1) := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.rayParity_eq_of_faceAdj_top d hclosed hsimple a b hadj

/--
[rayParity_eq_of_faceAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma rayParity_eq_of_faceAdj_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {f g : Site 2}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hadj : (walkRegionGraph d hclosed hsimple).Adj f g) :
-- imply
  rayParity d (f 0) (f 1) = rayParity d (g 0) (g 1) := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.rayParity_eq_of_faceAdj d hclosed hsimple hadj

/--
[rayParity_eq_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma rayParity_eq_of_reachable_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {f g : Site 2}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreach : (walkRegionGraph d hclosed hsimple).Reachable f g) :
-- imply
  rayParity d (f 0) (f 1) = rayParity d (g 0) (g 1) := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.rayParity_eq_of_reachable d hclosed hsimple hreach

/--
[lexInteriorIndex_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma lexInteriorIndex_spec_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4} :
-- imply
  d (lexInteriorIndex d hclosed hsimple hreflexfree - 1) = 1 ∧ d (lexInteriorIndex d hclosed hsimple hreflexfree) = 2 ∧ rayParity d ((pos d (lexInteriorIndex d hclosed hsimple hreflexfree)).1 - 1) ((pos d (lexInteriorIndex d hclosed hsimple hreflexfree)).2 - 1) = 1 := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.lexInteriorIndex_spec d

/--
[lexInteriorFace_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma lexInteriorFace_parity_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4} :
-- imply
  rayParity d (lexInteriorFace d hclosed hsimple hreflexfree 0) (lexInteriorFace d hclosed hsimple hreflexfree 1) = 1 := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.lexInteriorFace_parity d

/--
[outerBeacon_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma outerBeacon_parity_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4} :
-- imply
  rayParity d (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1) 0) (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1) 1) = 0 := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.outerBeacon_parity d

/--
[innerComponent_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma innerComponent_finite_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4} :
-- imply
  (innerComponent d hclosed hsimple hreflexfree).supp.Finite := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.innerComponent_finite d

/--
[componentCellSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma componentCellSet_finite_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4} :
-- imply
  (componentCellSet d hclosed hsimple hreflexfree).Finite := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.componentCellSet_finite d

/--
[mem_interiorCells](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma mem_interiorCells_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {p : ℤ × ℤ} :
-- imply
  p ∈ interiorCells d hclosed hsimple hreflexfree ↔ cellFace p ∈ (innerComponent d hclosed hsimple hreflexfree).supp := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.mem_interiorCells d p

/--
[mem_interiorCells_iff_rayParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean)
-/
@[path]
private lemma mem_interiorCells_iff_rayParity_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {p : ℤ × ℤ} :
-- imply
  p ∈ interiorCells d hclosed hsimple hreflexfree ↔ rayParity d p.1 p.2 = 1 := by
-- proof
  apply StatMech.Onsager.WalkCellRegion.mem_interiorCells_iff_rayParity d p


-- created on 2026-10-23
