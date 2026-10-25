import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part4
open StatMech StatMech.Universality


/--
[fkIsingSquareRadialPatchEdge_not_mem_perimeter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchEdge_not_mem_perimeter_eq
  {n m : Nat}
  {i j : Fin m}
-- given
  (hm : m ≤ n) :
-- imply
  (fkIsingSquareRadialPatchEdge n m hm i j).1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchEdge_not_mem_perimeter n m hm i j

/--
[fkIsingSquareBoundaryRadialPatchFullObservable_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservable_projection_eq
  {n m : Nat}
  {i j : Fin m}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (hm : m ≤ n) :
-- imply
  isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s))) (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservable_projection n m hn hm i j s

/--
[fkIsingSquareBoundaryRadialPatchFullValue_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullValue_of_even_eq
  {n m : Nat}
  {i j : Fin m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (h : Even (i.1 + j.1)) :
-- imply
  fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2 i j = FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue n m hn hm ⟨(i, j), h⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullValue_of_even n m hn hm hm2 i j h

/--
[fkIsingSquareBoundaryRadialPatchFullValue_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullValue_of_odd_eq
  {n m : Nat}
  {i j : Fin m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (h : ¬ Even (i.1 + j.1)) :
-- imply
  fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2 i j = FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue n m hn hm hm2 ⟨(i, j), h⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullValue_of_odd n m hn hm hm2 i j h

/--
[fkIsingSquareBoundaryRadialPatchIncidence_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchIncidence_gap_eq
  {n m : Nat}
  {i j : Fin m}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (hm : m ≤ n) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn (fkIsingSquareRadialPatchIncidence n m hn hm i j s)) - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn (fkIsingSquareRadialPatchIncidence n m hn hm i j s)) = Complex.normSq (isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s))) (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchIncidence_gap n m hn hm i j s

/--
[fkIsingSquareBoundaryRadialPatchIncidence_increment_eq_normSq_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchIncidence_increment_eq_normSq_projection_eq
  {n m : Nat}
  {i j : Fin m}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (hm : m ≤ n) :
-- imply
  fkIsingSquareBoundaryLayerRadialIncrement n hn (fkIsingSquareRadialPatchIncidence n m hn hm i j s) = Complex.normSq (isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s))) (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchIncidence_increment_eq_normSq_projection n m hn hm i j s

/--
[fkIsingSquareRadialPatchDualFullFace_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualFullFace_adj_iff_eq
  {n m : Nat}
  {p q : FKIsingSquareRadialPatchDualNode m}
-- given
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  (fkIsingSquareFullFaceGraph n).Adj (fkIsingSquareRadialPatchDualFullFace n m hm hm2 p) (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q) ↔ (fkIsingSquareRadialPatchDualGraph m).Adj p q := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualFullFace_adj_iff n m hm hm2 p q

/--
[fkIsingSquareBoundaryRadialPatchPrimal_laplacian_eq_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchPrimal_laplacian_eq_full_eq
  {n m : Nat}
  {p : FKIsingSquareRadialPatchPrimalNode m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hp : ¬ fkIsingSquareRadialPatchPrimalBoundary m p) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareRadialPatchPrimalGraph n m hm) (FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue n m hn hm) p = isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareRadialPatchPrimalFullVertex n m hm p) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchPrimal_laplacian_eq_full n m hn hm p hp

/--
[fkIsingSquareBoundaryRadialPatchDual_laplacian_eq_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchDual_laplacian_eq_full_eq
  {n m : Nat}
  {p : FKIsingSquareRadialPatchDualNode m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hp : ¬ fkIsingSquareRadialPatchDualBoundary m p) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareRadialPatchDualGraph m) (FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue n m hn hm hm2) p = isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareRadialPatchDualFullFace n m hm hm2 p) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchDual_laplacian_eq_full n m hn hm hm2 p hp

/--
[fkIsingSquareBoundaryRadialPatchPrimal_superharmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchPrimal_superharmonicOn_eq
  {n m : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n) :
-- imply
  IsingFiniteGraphSuperharmonicOn (fkIsingSquareRadialPatchPrimalGraph n m hm) (fkIsingSquareRadialPatchPrimalBoundary m) (FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue n m hn hm) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchPrimal_superharmonicOn n m hn hm

/--
[fkIsingSquareBoundaryRadialPatchDual_subharmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchDual_subharmonicOn_eq
  {n m : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  IsingFiniteGraphSubharmonicOn (fkIsingSquareRadialPatchDualGraph m) (fkIsingSquareRadialPatchDualBoundary m) (FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue n m hn hm hm2) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchDual_subharmonicOn n m hn hm hm2

/--
[fkIsingSquareBoundaryRadialPatchPrimal_physicalDeepVariation_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchPrimal_physicalDeepVariation_sq_le_eq
  {n m : Nat}
  {r : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r) :
-- imply
  ((1 / (m : Real)) * ∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r, |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue n m hn hm d.snd - FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue n m hn hm d.fst|) ^ 2 ≤ 64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchPrimal_physicalDeepVariation_sq_le n m hn hm hm2 r hr

/--
[fkIsingSquareBoundaryRadialPatchDual_physicalDeepVariation_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchDual_physicalDeepVariation_sq_le_eq
  {n m : Nat}
  {r : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r) :
-- imply
  ((1 / (m : Real)) * ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r, |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue n m hn hm hm2 d.snd - FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue n m hn hm hm2 d.fst|) ^ 2 ≤ 64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchDual_physicalDeepVariation_sq_le n m hn hm hm2 r hr

/--
[fkIsingSquareBoundaryRadialPatchFullValue_horizontal_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullValue_horizontal_increment_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hi : i + 1 < m)
  (hj : j < m) :
-- imply
  fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2 ⟨i + 1, hi⟩ ⟨j, hj⟩ - fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2 ⟨i, by omega⟩ ⟨j, hj⟩ = fkIsingSquareBoundaryRadialPatchHorizontalSignedIncrement n m hn hm (by omega) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullValue_horizontal_increment n m hn hm hm2 i j hi hj

/--
[fkIsingSquareBoundaryRadialPatchFullValue_vertical_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullValue_vertical_increment_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hi : i < m)
  (hj : j + 1 < m) :
-- imply
  fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2 ⟨i, hi⟩ ⟨j + 1, hj⟩ - fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2 ⟨i, hi⟩ ⟨j, by omega⟩ = fkIsingSquareBoundaryRadialPatchVerticalSignedIncrement n m hn hm (by omega) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullValue_vertical_increment n m hn hm hm2 i j hi hj

/--
[fkIsingSquareBoundaryRadialPatch_normSq_full_le_diagonalVariation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatch_normSq_full_le_diagonalVariation_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hi : i + 1 < m)
  (hj : j + 1 < m) :
-- imply
  Complex.normSq (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩) ≤ 2 * (|fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2 ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ - fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2 ⟨i, by omega⟩ ⟨j, by omega⟩| + |fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2 ⟨i + 1, hi⟩ ⟨j, by omega⟩ - fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2 ⟨i, by omega⟩ ⟨j + 1, hj⟩|) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatch_normSq_full_le_diagonalVariation n m hn hm hm2 i j hi hj

/--
[fkIsingSquareBoundaryRadialPatchCellDiagonalVariation_eq_cellDarts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchCellDiagonalVariation_eq_cellDarts_eq
  {n m : Nat}
  {c : FKIsingSquareRadialPatchInteriorCell m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  fkIsingSquareBoundaryRadialPatchCellDiagonalVariation n m hn hm hm2 c = := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchCellDiagonalVariation_eq_cellDarts n m hn hm hm2 c

/--
[fkIsingSquareBoundaryRadialPatch_normSq_full_le_cellDiagonalVariation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatch_normSq_full_le_cellDiagonalVariation_eq
  {n m : Nat}
  {c : FKIsingSquareRadialPatchInteriorCell m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  Complex.normSq (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩) ≤ 2 * fkIsingSquareBoundaryRadialPatchCellDiagonalVariation n m hn hm hm2 c := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatch_normSq_full_le_cellDiagonalVariation n m hn hm hm2 c

/--
[fkIsingSquareBoundaryRadialPatch_deepCellDiagonalVariation_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatch_deepCellDiagonalVariation_sum_le_eq
  {n m : Nat}
  {r : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r, fkIsingSquareBoundaryRadialPatchCellDiagonalVariation n m hn hm hm2 c) ≤ (∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r, |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue n m hn hm d.snd - FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue n m hn hm d.fst|) + ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r, := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatch_deepCellDiagonalVariation_sum_le n m hn hm hm2 r

/--
[fkIsingSquareBoundaryRadialPatch_deepCell_normSq_sum_le_variation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatch_deepCell_normSq_sum_le_variation_eq
  {n m : Nat}
  {r : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r, Complex.normSq (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)) ≤ 2 * ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r, |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue n m hn hm d.snd - FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue n m hn hm d.fst|) + ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r, |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue n m hn hm hm2 d.snd - FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue n m hn hm hm2 d.fst|) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatch_deepCell_normSq_sum_le_variation n m hn hm hm2 r

/--
[fkIsingSquareBoundaryRadialPatchWindowCarrier_normalized_normSq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchWindowCarrier_normalized_normSq_le_eq
  {n m baseI baseJ R : Nat}
  {mesh : Real}
  {p : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hmesh : 0 < mesh) :
-- imply
  Complex.normSq ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).normalizedFermionicObservable mesh (fkIsingSquareRadialPatchWindowCarrier n m baseI baseJ R hm hfitI hfitJ p)) ≤ Complex.normSq (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨baseI + p.1.1, by have := p.1.2; omega⟩ ⟨baseJ + p.2.1, by have := p.2.2; omega⟩ / (Real.sqrt (2 * mesh) : Complex)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchWindowCarrier_normalized_normSq_le n m baseI baseJ R mesh hn hm hfitI hfitJ hmesh p


-- created on 2026-10-23
