import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalGhostEnergy
open StatMech StatMech.Universality


/--
[fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_ghostComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalGhostEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_ghostComparison_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r)
  (hprimalLower : ∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p)
  (hdualUpper : ∀ q, fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) :
-- imply
  (((1 / (m : Real)) ^ 2) * ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r, Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ / (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ^ 2 ≤ 256 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_ghostComparison n m hn hm hm2 r hr base hprimalLower hdualUpper

/--
[fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_fixedFraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalGhostEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_fixedFraction_eq
  {n m : Nat}
  {r : Nat}
  {base K : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r)
  (hK : 0 ≤ K)
  (hmr : (m : Real) ≤ K * (r : Real))
  (hprimalLower : ∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p)
  (hdualUpper : ∀ q, fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) :
-- imply
  (((1 / (m : Real)) ^ 2) * ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r, Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ / (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ^ 2 ≤ 256 * K ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_fixedFraction n m hn hm hm2 r hr base K hK hmr hprimalLower hdualUpper

/--
[fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_fullSquareGhost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalGhostEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_fullSquareGhost_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
  {vertexH : FKIsingSquareFullVertexNode n → Real}
  {faceH : FKIsingSquareFullFaceNode n → Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r)
  (hvertexModified : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x → isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) vertexH x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - vertexH x) ≤ 0)
  (hvertexFixed : ∀ x, fkIsingSquareFullVertexFixedBoundary n x → 0 ≤ vertexH x)
  (hfaceModified : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c → 0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) faceH c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - faceH c))
  (hfaceFixed : ∀ c, fkIsingSquareFullFaceFixedBoundary n c → faceH c ≤ 1)
  (hprimalRestriction : ∀ p, fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p = vertexH (fkIsingSquareRadialPatchPrimalFullVertex n m hm p))
  (hdualRestriction : ∀ q, fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q = faceH (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q)) :
-- imply
  (((1 / (m : Real)) ^ 2) * ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r, Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ / (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ^ 2 ≤ 256 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_fullSquareGhost n m hn hm hm2 r hr base vertexH faceH hvertexModified hvertexFixed hfaceModified hfaceFixed hprimalRestriction hdualRestriction

/--
[fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_fullSquareGhost_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalGhostEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_fullSquareGhost_compatible_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
  {vertexH : FKIsingSquareFullVertexNode n → Real}
  {faceH : FKIsingSquareFullFaceNode n → Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r)
  (hvertexModified : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x → isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) vertexH x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - vertexH x) ≤ 0)
  (hvertexFixed : ∀ x, fkIsingSquareFullVertexFixedBoundary n x → 0 ≤ vertexH x)
  (hfaceModified : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c → 0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) faceH c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - faceH c))
  (hfaceFixed : ∀ c, fkIsingSquareFullFaceFixedBoundary n c → faceH c ≤ 1)
  (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
  (hbase : fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH ⟨0, by omega⟩ ⟨0, by omega⟩ = base) :
-- imply
  (((1 / (m : Real)) ^ 2) * ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r, Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ / (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ^ 2 ≤ 256 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_fullSquareGhost_compatible n m hn hm hm2 r hr base vertexH faceH hvertexModified hvertexFixed hfaceModified hfaceFixed hcompatible hbase


-- created on 2026-10-23
