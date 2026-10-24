import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization
open StatMech StatMech.Universality


/--
[fkIsingSquareRadialPatchEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWindowRealization.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchEdge_injective_eq
  {n m : Nat}
-- given
  (hm : m ≤ n) :
-- imply
  Function.Injective (fun p : Fin m × Fin m ↦ fkIsingSquareRadialPatchEdge n m hm p.1 p.2) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchEdge_injective n m hm

/--
[fkIsingSquareRadialPatchWindowCarrier_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWindowRealization.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchWindowCarrier_injective_eq
  {n m baseI baseJ R : Nat}
-- given
  (hm : m ≤ n)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m) :
-- imply
  Function.Injective (fkIsingSquareRadialPatchWindowCarrier n m baseI baseJ R hm hfitI hfitJ) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchWindowCarrier_injective n m baseI baseJ R hm hfitI hfitJ

/--
[fkIsingSquareRadialPatchWindowCarrier_normalized_normSq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWindowRealization.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchWindowCarrier_normalized_normSq_le_eq
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
  Complex.normSq ((fkIsingSquareWiredDobrushinDomain n hn).normalizedFermionicObservable mesh (fkIsingSquareRadialPatchWindowCarrier n m baseI baseJ R hm hfitI hfitJ p)) ≤ Complex.normSq (fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p / (Real.sqrt (2 * mesh) : Complex)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchWindowCarrier_normalized_normSq_le n m baseI baseJ R mesh hn hm hfitI hfitJ hmesh p

/--
[fkIsingSquareRadialPatchWindowCarrier_average_normSq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWindowRealization.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchWindowCarrier_average_normSq_le_eq
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
  (∑ a ∈ Finset.univ.map (fkIsingSquareRadialPatchWindowCarrierEmbedding n m baseI baseJ R hm hfitI hfitJ), Complex.normSq ((fkIsingSquareWiredDobrushinDomain n hn).normalizedFermionicObservable (1 / (m : Real)) a)) ≤ ((Finset.univ.map (fkIsingSquareRadialPatchWindowCarrierEmbedding n m baseI baseJ R hm hfitI hfitJ)).card : Real) * (16 * K * Q ^ 2) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchWindowCarrier_average_normSq_le n m baseI baseJ R r K Q base hn hm hm2 hr hfitI hfitJ hK hQ hmr hmR hdeep hprimalLower hdualUpper


-- created on 2026-10-23
