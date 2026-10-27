import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactVariation.Part2
open StatMech StatMech.Universality


/--
[fkIsingSquareRadialPatchPrimalBoundary_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalBoundary_nonempty_eq
  {m : Nat}
-- given
  (hm : 0 < m) :
-- imply
  ∃ p : FKIsingSquareRadialPatchPrimalNode m, fkIsingSquareRadialPatchPrimalBoundary m p := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalBoundary_nonempty m hm

/--
[fkIsingSquareRadialPatchDualBoundary_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualBoundary_nonempty_eq
  {m : Nat}
-- given
  (hm : 2 ≤ m) :
-- imply
  ∃ p : FKIsingSquareRadialPatchDualNode m, fkIsingSquareRadialPatchDualBoundary m p := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualBoundary_nonempty m hm

/--
[fkIsingSquareRadialPatchPrimalTentCutoff_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalTentCutoff_support_eq
  {n m : Nat}
  {r : Nat}
-- given
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  ∀ p, fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r p ≠ 0 → ¬ fkIsingSquareRadialPatchPrimalBoundary m p := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalTentCutoff_support n m hm hmpos r

/--
[fkIsingSquareRadialPatchDualTentCutoff_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualTentCutoff_support_eq
  {m : Nat}
  {r : Nat}
-- given
  (hm : 2 ≤ m) :
-- imply
  ∀ p, fkIsingSquareRadialPatchDualTentCutoff m hm r p ≠ 0 → ¬ fkIsingSquareRadialPatchDualBoundary m p := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualTentCutoff_support m hm r

/--
[fkIsingSquareRadialPatchPrimalTentCutoff_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalTentCutoff_lipschitz_eq
  {n m : Nat}
  {r : Nat}
  {d : (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart}
-- given
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hr : 0 < r) :
-- imply
  |fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r d.snd - fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r d.fst| ≤ 1 / (r : Real) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalTentCutoff_lipschitz n m hm hmpos r hr d

/--
[fkIsingSquareRadialPatchDualTentCutoff_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualTentCutoff_lipschitz_eq
  {m : Nat}
  {r : Nat}
  {d : (fkIsingSquareRadialPatchDualGraph m).Dart}
-- given
  (hm : 2 ≤ m)
  (hr : 0 < r) :
-- imply
  |fkIsingSquareRadialPatchDualTentCutoff m hm r d.snd - fkIsingSquareRadialPatchDualTentCutoff m hm r d.fst| ≤ 1 / (r : Real) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualTentCutoff_lipschitz m hm r hr d

/--
[fkIsingSquareRadialPatchPrimalTentCutoff_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalTentCutoff_one_eq
  {n m : Nat}
  {r : Nat}
-- given
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hr : 0 < r) :
-- imply
  ∀ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r, (1 : Real) ≤ fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r d.snd := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalTentCutoff_one n m hm hmpos r hr

/--
[fkIsingSquareRadialPatchDualTentCutoff_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualTentCutoff_one_eq
  {m : Nat}
  {r : Nat}
-- given
  (hm : 2 ≤ m)
  (hr : 0 < r) :
-- imply
  ∀ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm r, (1 : Real) ≤ fkIsingSquareRadialPatchDualTentCutoff m hm r d.snd := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualTentCutoff_one m hm r hr

/--
[fkIsingSquareRadialPatchPrimalTentCutoff_energy_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalTentCutoff_energy_le_eq
  {n m : Nat}
  {r : Nat}
-- given
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hr : 0 < r) :
-- imply
  isingFiniteGraphDartSum (fkIsingSquareRadialPatchPrimalGraph n m hm) (fun x y ↦ (fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r y - fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r x) ^ 2) ≤ 4 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalTentCutoff_energy_le n m hm hmpos r hr

/--
[fkIsingSquareRadialPatchDualTentCutoff_energy_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualTentCutoff_energy_le_eq
  {m : Nat}
  {r : Nat}
-- given
  (hm : 2 ≤ m)
  (hr : 0 < r) :
-- imply
  isingFiniteGraphDartSum (fkIsingSquareRadialPatchDualGraph m) (fun x y ↦ (fkIsingSquareRadialPatchDualTentCutoff m hm r y - fkIsingSquareRadialPatchDualTentCutoff m hm r x) ^ 2) ≤ 4 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualTentCutoff_energy_le m hm r hr

/--
[fkIsingSquareRadialPatchPrimalDeepDarts_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalDeepDarts_card_le_eq
  {n m : Nat}
  {r : Nat}
-- given
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  (fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r).card ≤ 4 * m ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalDeepDarts_card_le n m hm hmpos r

/--
[fkIsingSquareRadialPatchDualDeepDarts_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualDeepDarts_card_le_eq
  {m : Nat}
  {r : Nat}
-- given
  (hm : 2 ≤ m) :
-- imply
  (fkIsingSquareRadialPatchDualDeepDarts m hm r).card ≤ 4 * m ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualDeepDarts_card_le m hm r

/--
[fkIsingSquareRadialPatchPrimal_deepVariation_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimal_deepVariation_sq_le_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hr : 0 < r) :
-- imply
  (∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r, |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd - fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|) ^ 2 ≤ 256 * (#(fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r) : Real) * (m : Real) ^ 4 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimal_deepVariation_sq_le n m hn hm hmpos r hr base

/--
[fkIsingSquareRadialPatchDual_deepVariation_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDual_deepVariation_sq_le_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r) :
-- imply
  (∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r, |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) ^ 2 ≤ 256 * (#(fkIsingSquareRadialPatchDualDeepDarts m hm2 r) : Real) * (m : Real) ^ 4 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDual_deepVariation_sq_le n m hn hm hm2 r hr base

/--
[fkIsingSquareRadialPatchPrimal_normalizedDeepVariation_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimal_normalizedDeepVariation_sq_le_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hr : 0 < r) :
-- imply
  ((1 / (m : Real) ^ 2) * ∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r, |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd - fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|) ^ 2 ≤ 1024 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimal_normalizedDeepVariation_sq_le n m hn hm hmpos r hr base

/--
[fkIsingSquareRadialPatchDual_normalizedDeepVariation_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDual_normalizedDeepVariation_sq_le_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r) :
-- imply
  ((1 / (m : Real) ^ 2) * ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r, |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) ^ 2 ≤ 1024 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDual_normalizedDeepVariation_sq_le n m hn hm hm2 r hr base

/--
[fkIsingSquareRadialPatchPrimal_normalizedDeepVariation_fixedFraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimal_normalizedDeepVariation_fixedFraction_eq
  {n m : Nat}
  {r K : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hr : 0 < r)
  (hfrac : m ≤ K * r) :
-- imply
  ((1 / (m : Real) ^ 2) * ∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r, |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd - fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|) ^ 2 ≤ 1024 * (K : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimal_normalizedDeepVariation_fixedFraction n m hn hm hmpos r K hr hfrac base

/--
[fkIsingSquareRadialPatchDual_normalizedDeepVariation_fixedFraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDual_normalizedDeepVariation_fixedFraction_eq
  {n m : Nat}
  {r K : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r)
  (hfrac : m ≤ K * r) :
-- imply
  ((1 / (m : Real) ^ 2) * ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r, |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) ^ 2 ≤ 1024 * (K : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDual_normalizedDeepVariation_fixedFraction n m hn hm hm2 r K hr hfrac base


-- created on 2026-10-23
