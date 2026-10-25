import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalAverageAnchor
open StatMech StatMech.Universality


/--
[fkIsingSquareRadialPatchPhysicalNormalizedWindow_energy_le_deepCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalAverageAnchor.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPhysicalNormalizedWindow_energy_le_deepCell_eq
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
  mesh ^ 2 * ∑ p : IsingLeapfrogBox R, Complex.normSq (fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p / (Real.sqrt (2 * mesh) : Complex)) ≤ mesh ^ 2 * ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r, Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ / (Real.sqrt (2 * mesh) : Complex)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPhysicalNormalizedWindow_energy_le_deepCell n m baseI baseJ R mesh hn hm hm2 hfitI hfitJ r hdeep

/--
[fkIsingSquareRadialPatchPhysicalNormalizedWindow_average_normSq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalAverageAnchor.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPhysicalNormalizedWindow_average_normSq_le_eq
  {n m baseI baseJ R r : Nat}
  {K Q base : Real}
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
  (hdeep : ∀ p : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
  (hprimalLower : ∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p)
  (hdualUpper : ∀ q, fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) :
-- imply
  (∑ p : IsingLeapfrogBox R, Complex.normSq (fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p / (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ≤ (Fintype.card (IsingLeapfrogBox R) : Real) * (16 * K * Q ^ 2) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPhysicalNormalizedWindow_average_normSq_le n m baseI baseJ R r K Q base hn hm hm2 hr hfitI hfitJ hK hQ hmr hmR hdeep hprimalLower hdualUpper


-- created on 2026-10-23
