import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryAverage
open StatMech StatMech.Universality


/--
[fkIsingSquareRadialPatchWindowCell_mem_deepCells_of_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryAverage.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchWindowCell_mem_deepCells_of_margin_eq
  {n m baseI baseJ R r : Nat}
  {p : IsingLeapfrogBox R}
-- given
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hleft : r ≤ baseI)
  (hbottom : r ≤ baseJ)
  (hright : baseI + R + 1 + r < m)
  (htop : baseJ + R + 1 + r < m) :
-- imply
  fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchWindowCell_mem_deepCells_of_margin n m baseI baseJ R r hm hm2 hfitI hfitJ hleft hbottom hright htop p

/--
[fkIsingSquareBoundaryRadialPatchNormalizedWindow_energy_le_deepCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryAverage.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchNormalizedWindow_energy_le_deepCell_eq
  {n m baseI baseJ R : Nat}
  {mesh : Real}
  {r : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hdeep : ∀ p : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r) :
-- imply
  (∑ p : IsingLeapfrogBox R, Complex.normSq (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨baseI + p.1.1, by have := p.1.2; omega⟩ ⟨baseJ + p.2.1, by have := p.2.2; omega⟩ / (Real.sqrt (2 * mesh) : Complex))) ≤ ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r, Complex.normSq (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ / (Real.sqrt (2 * mesh) : Complex)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchNormalizedWindow_energy_le_deepCell n m baseI baseJ R mesh hn hm hm2 hfitI hfitJ r hdeep

/--
[fkIsingSquareBoundaryRadialPatch_deepCell_normalizedEnergy_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryAverage.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatch_deepCell_normalizedEnergy_le_eq
  {n m r : Nat}
  {K : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r)
  (hmr : (m : Real) ≤ K * (r : Real)) :
-- imply
  (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r, Complex.normSq (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ / (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ≤ 16 * K * (m : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatch_deepCell_normalizedEnergy_le n m r K hn hm hm2 hr hmr

/--
[fkIsingSquareBoundaryRadialPatchNormalizedWindow_average_normSq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryAverage.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchNormalizedWindow_average_normSq_le_eq
  {n m baseI baseJ R r : Nat}
  {K Q : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hK : 0 ≤ K)
  (hQ : 0 ≤ Q)
  (hmr : (m : Real) ≤ K * (r : Real))
  (hmR : (m : Real) ≤ Q * (R + 1 : Nat))
  (hdeep : ∀ p : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r) :
-- imply
  (∑ p : IsingLeapfrogBox R, Complex.normSq (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨baseI + p.1.1, by have := p.1.2; omega⟩ ⟨baseJ + p.2.1, by have := p.2.2; omega⟩ / (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ≤ (Fintype.card (IsingLeapfrogBox R) : Real) * (16 * K * Q ^ 2) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchNormalizedWindow_average_normSq_le n m baseI baseJ R r K Q hn hm hm2 hr hfitI hfitJ hK hQ hmr hmR hdeep

/--
[normalizedFermionicObservable_normSq_anti_mesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryAverage.lean)
-/
@[path]
private lemma normalizedFermionicObservable_normSq_anti_mesh_eq
  {z : Complex}
  {mesh₀ mesh : Real}
-- given
  (hmesh₀ : 0 < mesh₀)
  (hle : mesh₀ ≤ mesh) :
-- imply
  Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) ≤ Complex.normSq (z / (Real.sqrt (2 * mesh₀) : Complex)) := by
-- proof
  apply StatMech.Universality.normalizedFermionicObservable_normSq_anti_mesh z hmesh₀ hle

/--
[fkIsingSquareBoundaryRadialPatchWindowCarrier_average_normSq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryAverage.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchWindowCarrier_average_normSq_le_eq
  {n m baseI baseJ R r : Nat}
  {mesh K Q : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hmesh : 0 < mesh)
  (hmeshLower : 1 / (m : Real) ≤ mesh)
  (hK : 0 ≤ K)
  (hQ : 0 ≤ Q)
  (hmr : (m : Real) ≤ K * (r : Real))
  (hmR : (m : Real) ≤ Q * (R + 1 : Nat))
  (hdeep : ∀ p : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r) :
-- imply
  (∑ a ∈ Finset.univ.map (fkIsingSquareRadialPatchWindowCarrierEmbedding n m baseI baseJ R hm hfitI hfitJ), Complex.normSq ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).normalizedFermionicObservable mesh a)) ≤ ((Finset.univ.map (fkIsingSquareRadialPatchWindowCarrierEmbedding n m baseI baseJ R hm hfitI hfitJ)).card : Real) * (16 * K * Q ^ 2) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchWindowCarrier_average_normSq_le n m baseI baseJ R r mesh K Q hn hm hm2 hr hfitI hfitJ hmesh hmeshLower hK hQ hmr hmR hdeep


-- created on 2026-10-23
