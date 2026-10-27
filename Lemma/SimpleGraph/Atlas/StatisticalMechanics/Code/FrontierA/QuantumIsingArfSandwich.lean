import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingArfSandwich
open StatMech StatMech.FrontierA


/--
[norm_le_arfSectorNormMax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingArfSandwich.lean)
-/
@[path]
private lemma norm_le_arfSectorNormMax_eq
  {a b : Fin 2}
-- given
  (sector : Fin 2 -> Fin 2 -> Complex) :
-- imply
  ‖sector a b‖ <= arfSectorNormMax sector := by
-- proof
  apply StatMech.FrontierA.norm_le_arfSectorNormMax sector a b

/--
[arfSectorNormMax_le_and_le_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingArfSandwich.lean)
-/
@[path]
private lemma arfSectorNormMax_le_and_le_two_mul_eq
  {Z : Real}
-- given
  (sector : Fin 2 -> Fin 2 -> Complex)
  (hZ : 0 < Z)
  (hdom : forall a b, ‖sector a b‖ <= Z)
  (harf : (2 * Z : Real) = sector 1 1 + sector 0 1 + sector 1 0 - sector 0 0) :
-- imply
  arfSectorNormMax sector <= Z ∧ Z <= 2 * arfSectorNormMax sector := by
-- proof
  apply StatMech.FrontierA.arfSectorNormMax_le_and_le_two_mul Z sector hZ hdom harf

/--
[arfSector_log_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingArfSandwich.lean)
-/
@[path]
private lemma arfSector_log_sandwich_eq
  {Z : Real}
-- given
  (sector : Fin 2 -> Fin 2 -> Complex)
  (hZ : 0 < Z)
  (hdom : forall a b, ‖sector a b‖ <= Z)
  (harf : (2 * Z : Real) = sector 1 1 + sector 0 1 + sector 1 0 - sector 0 0) :
-- imply
  Real.log (arfSectorNormMax sector) <= Real.log Z ∧ Real.log Z <= Real.log (arfSectorNormMax sector) + Real.log 2 := by
-- proof
  apply StatMech.FrontierA.arfSector_log_sandwich Z sector hZ hdom harf

/--
[arfSector_normalizedLog_gap_tendsto_zero_of_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingArfSandwich.lean)
-/
@[path]
private lemma arfSector_normalizedLog_gap_tendsto_zero_of_eventually_eq
-- given
  (Z : Nat -> Real)
  (sector : Nat -> Fin 2 -> Fin 2 -> Complex)
  (hZ : ∀ᶠ n in Filter.atTop, 0 < Z n)
  (hdom : ∀ᶠ n in Filter.atTop, forall a b, ‖sector n a b‖ <= Z n)
  (harf : ∀ᶠ n in Filter.atTop, (2 * Z n : Real) = sector n 1 1 + sector n 0 1 + sector n 1 0 - sector n 0 0) :
-- imply
  Filter.Tendsto (fun n : Nat => (Real.log (Z n) - Real.log (arfSectorNormMax (sector n))) / (n + 1 : Real)) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.arfSector_normalizedLog_gap_tendsto_zero_of_eventually Z sector hZ hdom harf

/--
[arfSector_normalizedLog_gap_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingArfSandwich.lean)
-/
@[path]
private lemma arfSector_normalizedLog_gap_tendsto_zero_eq
-- given
  (Z : Nat -> Real)
  (sector : Nat -> Fin 2 -> Fin 2 -> Complex)
  (hZ : forall n, 0 < Z n)
  (hdom : forall n a b, ‖sector n a b‖ <= Z n)
  (harf : forall n, (2 * Z n : Real) = sector n 1 1 + sector n 0 1 + sector n 1 0 - sector n 0 0) :
-- imply
  Filter.Tendsto (fun n : Nat => (Real.log (Z n) - Real.log (arfSectorNormMax (sector n))) / (n + 1 : Real)) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.arfSector_normalizedLog_gap_tendsto_zero Z sector hZ hdom harf


-- created on 2026-10-23
