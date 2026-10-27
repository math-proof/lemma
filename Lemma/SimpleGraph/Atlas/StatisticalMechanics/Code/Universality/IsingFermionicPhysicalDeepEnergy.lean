import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDeepEnergy.Part4
open StatMech StatMech.Universality


/--
[fkIsingSquareRadialPatchCellPrimalDart_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDeepEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchCellPrimalDart_injective_eq
  {n m : Nat}
-- given
  (hm : m ≤ n) :
-- imply
  Function.Injective (fkIsingSquareRadialPatchCellPrimalDart n m hm) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchCellPrimalDart_injective n m hm

/--
[fkIsingSquareRadialPatchCellDualDart_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDeepEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchCellDualDart_injective_eq
  {m : Nat} :
-- imply
  Function.Injective (fkIsingSquareRadialPatchCellDualDart m) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchCellDualDart_injective m

/--
[fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation_eq_cellDarts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDeepEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation_eq_cellDarts_eq
  {n m : Nat}
  {base : Real}
  {c : FKIsingSquareRadialPatchInteriorCell m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation n m hn hm hmpos c.1.1 c.2.1 = := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation_eq_cellDarts n m hn hm hmpos base c

/--
[fkIsingSquareRadialPatch_deepCellDiagonalVariation_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDeepEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_deepCellDiagonalVariation_sum_le_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r, fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation n m hn hm (by omega) c.1.1 c.2.1) ≤ (∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r, |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) + ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r, := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_deepCellDiagonalVariation_sum_le n m hn hm hm2 r base

/--
[fkIsingSquareRadialPatch_deepCell_normSq_sum_le_variation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDeepEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_deepCell_normSq_sum_le_variation_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r, Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)) ≤ 2 * ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r, |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) + ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r, |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_deepCell_normSq_sum_le_variation n m hn hm hm2 r base

/--
[fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDeepEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_le_eq
  {n m : Nat}
  {mesh : Real}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hmesh : 0 < mesh) :
-- imply
  mesh ^ 2 * ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r, Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ / (Real.sqrt (2 * mesh) : Complex)) ≤ mesh * ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r, |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) + ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r, |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_le n m mesh hn hm hm2 hmesh r base

/--
[fkIsingSquareRadialPatchWindowCell_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDeepEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchWindowCell_injective_eq
  {m baseI baseJ R : Nat}
-- given
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m) :
-- imply
  Function.Injective (fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchWindowCell_injective m baseI baseJ R hfitI hfitJ

/--
[fkIsingSquareRadialPatchFullObservableWindow_deep_energy_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDeepEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchFullObservableWindow_deep_energy_le_eq
  {n m baseI baseJ R : Nat}
  {mesh : Real}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hmesh : 0 < mesh)
  (hdeep : ∀ p : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r) :
-- imply
  mesh ^ 2 * ∑ p : IsingLeapfrogBox R, Complex.normSq (fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p / (Real.sqrt (2 * mesh) : Complex)) ≤ mesh * ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r, |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) + ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r, |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchFullObservableWindow_deep_energy_le n m baseI baseJ R mesh hn hm hm2 hfitI hfitJ hmesh r base hdeep

/--
[fkIsingSquareRadialPatchFullObservableWindow_deep_diffusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDeepEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchFullObservableWindow_deep_diffusive_eq
  {n m baseI baseJ R rho : Nat}
  {mesh : Real}
  {r : Nat}
  {base : Real}
  {p p' : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hmesh : 0 < mesh)
  (hdeep : ∀ q : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
  (hrho : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  mesh ^ 2 * Complex.normSq (fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p / (Real.sqrt (2 * mesh) : Complex) - fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p' / (Real.sqrt (2 * mesh) : Complex)) ≤ (1032080 / (rho : Real) ^ 3) * mesh * ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r, |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) + ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r, |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchFullObservableWindow_deep_diffusive n m baseI baseJ R rho mesh hn hm hm2 hfitI hfitJ hmesh r base hdeep p p' hrho hp hp' hpp'


-- created on 2026-10-23
