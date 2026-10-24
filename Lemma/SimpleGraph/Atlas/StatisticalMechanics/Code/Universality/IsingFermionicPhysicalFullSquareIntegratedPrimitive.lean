import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareFullIntegratedPrimitive


/--
[shiftedCoordinate_coordinateIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma shiftedCoordinate_coordinateIndex_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hq : FKIsingSquareFullDiamond n q) :
-- imply
  shiftedCoordinate n (coordinateIndex n q).1 (coordinateIndex n q).2 = q := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate_coordinateIndex n q hq

/--
[diamondCell_of_row_interval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma diamondCell_of_row_interval_eq
  {n i j k : Nat}
-- given
  (h0 : FKIsingSquareFullDiamond n (shiftedCoordinate n i j))
  (h1 : FKIsingSquareFullDiamond n (shiftedCoordinate n i (j + 1)))
  (hk : (2 * n ≤ k ∧ k < i) ∨ (i ≤ k ∧ k < 2 * n)) :
-- imply
  FKIsingSquareFullDiamondCell n (shiftedCoordinate n k j) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.diamondCell_of_row_interval n i j k h0 h1 hk

/--
[primitiveNat_horizontal_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma primitiveNat_horizontal_increment_eq
  {n : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n) :
-- imply
  primitiveNat n hn (i + 1) j - primitiveNat n hn i j = horizontalNat n hn i j := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.primitiveNat_horizontal_increment n hn i j

/--
[primitiveNat_vertical_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma primitiveNat_vertical_increment_eq
  {n : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (h0 : FKIsingSquareFullDiamond n (shiftedCoordinate n i j))
  (h1 : FKIsingSquareFullDiamond n (shiftedCoordinate n i (j + 1))) :
-- imply
  primitiveNat n hn i (j + 1) - primitiveNat n hn i j = verticalNat n hn i j := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.primitiveNat_vertical_increment n hn i j h0 h1

/--
[coordinateIndex_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma coordinateIndex_east_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hq : FKIsingSquareFullDiamond n q) :
-- imply
  coordinateIndex n (q.1 + 1, q.2) = ((coordinateIndex n q).1 + 1, (coordinateIndex n q).2) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.coordinateIndex_east n q hq

/--
[coordinateIndex_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma coordinateIndex_north_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hq : FKIsingSquareFullDiamond n q) :
-- imply
  coordinateIndex n (q.1, q.2 + 1) = ((coordinateIndex n q).1, (coordinateIndex n q).2 + 1) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.coordinateIndex_north n q hq

/--
[coordinatePrimitive_horizontal_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma coordinatePrimitive_horizontal_increment_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hn : 0 < n)
  (hq : FKIsingSquareFullDiamond n q) :
-- imply
  coordinatePrimitive n hn (q.1 + 1, q.2) - coordinatePrimitive n hn q = fkIsingSquareFullHorizontalIncrement n hn q := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.coordinatePrimitive_horizontal_increment n hn q hq

/--
[coordinatePrimitive_vertical_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma coordinatePrimitive_vertical_increment_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hn : 0 < n)
  (hq : FKIsingSquareFullDiamond n q)
  (hqN : FKIsingSquareFullDiamond n (q.1, q.2 + 1)) :
-- imply
  coordinatePrimitive n hn (q.1, q.2 + 1) - coordinatePrimitive n hn q = fkIsingSquareFullVerticalIncrement n hn q := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.coordinatePrimitive_vertical_increment n hn q hq hqN

/--
[compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma compatible_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  FKIsingSquareFullPrimitiveCompatible n hn (vertexPrimitive n hn) (facePrimitive n hn) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.compatible n hn

/--
[face_sub_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma face_sub_vertex_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  facePrimitive n hn (fkIsingSquareFullFaceOfRadialIncidence n hn e) - vertexPrimitive n hn (fkIsingSquareInteriorRadialEndpoint n hn e) = fkIsingSquareInteriorRadialIncrement n hn e := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.face_sub_vertex n hn e

/--
[vertex_le_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma vertex_le_face_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  vertexPrimitive n hn (fkIsingSquareInteriorRadialEndpoint n hn e) ≤ facePrimitive n hn (fkIsingSquareFullFaceOfRadialIncidence n hn e) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.vertex_le_face n hn e

/--
[face_sub_vertex_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma face_sub_vertex_nonneg_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  0 ≤ facePrimitive n hn (fkIsingSquareFullFaceOfRadialIncidence n hn e) - vertexPrimitive n hn (fkIsingSquareInteriorRadialEndpoint n hn e) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.face_sub_vertex_nonneg n hn e

/--
[markedB_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma markedB_base_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  vertexPrimitive n hn (fkIsingSquareMarkedB n) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.markedB_base n hn

/--
[radialPatchPrimalValue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma radialPatchPrimalValue_eq_eq
  {n m : Nat}
  {p : FKIsingSquareRadialPatchPrimalNode m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) (radialPatchBase n m hn hm hm2) p = vertexPrimitive n hn (fkIsingSquareRadialPatchPrimalFullVertex n m hm p) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.radialPatchPrimalValue_eq n m hn hm hm2 p

/--
[radialPatchDualValue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma radialPatchDualValue_eq_eq
  {n m : Nat}
  {q : FKIsingSquareRadialPatchDualNode m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  fkIsingSquareRadialPatchDualValue n m hn hm (by omega) (radialPatchBase n m hn hm hm2) q = facePrimitive n hn (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.radialPatchDualValue_eq n m hn hm hm2 q

/--
[radialPatch_unitRange_of_fullSquareGhost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma radialPatch_unitRange_of_fullSquareGhost_eq
  {n m : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hvertexModified : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x → isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (vertexPrimitive n hn) x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - vertexPrimitive n hn x) ≤ 0)
  (hvertexFixed : ∀ x, fkIsingSquareFullVertexFixedBoundary n x → 0 ≤ vertexPrimitive n hn x)
  (hfaceModified : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c → 0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (facePrimitive n hn) c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - facePrimitive n hn c))
  (hfaceFixed : ∀ c, fkIsingSquareFullFaceFixedBoundary n c → facePrimitive n hn c ≤ 1) :
-- imply
  (∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) (radialPatchBase n m hn hm hm2) p ∧ fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) (radialPatchBase n m hn hm hm2) p ≤ 1) ∧ (∀ q, 0 ≤ fkIsingSquareRadialPatchDualValue n m hn hm (by omega) (radialPatchBase n m hn hm hm2) q ∧ fkIsingSquareRadialPatchDualValue n m hn hm (by omega) (radialPatchBase n m hn hm hm2) q ≤ 1) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.radialPatch_unitRange_of_fullSquareGhost n m hn hm hm2 hvertexModified hvertexFixed hfaceModified hfaceFixed

/--
[radialPatch_deepCell_energy_sq_le_of_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean)
-/
@[path]
private lemma radialPatch_deepCell_energy_sq_le_of_boundary_eq
  {n m : Nat}
  {r : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r)
  (hvertexModified : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x → isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (vertexPrimitive n hn) x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - vertexPrimitive n hn x) ≤ 0)
  (hvertexFixed : ∀ x, fkIsingSquareFullVertexFixedBoundary n x → 0 ≤ vertexPrimitive n hn x)
  (hfaceModified : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c → 0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (facePrimitive n hn) c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - facePrimitive n hn c))
  (hfaceFixed : ∀ c, fkIsingSquareFullFaceFixedBoundary n c → facePrimitive n hn c ≤ 1) :
-- imply
  (((1 / (m : Real)) ^ 2) * ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r, Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ / (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ^ 2 ≤ 256 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.radialPatch_deepCell_energy_sq_le_of_boundary n m hn hm hm2 r hr hvertexModified hvertexFixed hfaceModified hfaceFixed


-- created on 2026-10-23
