import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.PlusStateSpinProfileLimit
open MeasureTheory Filter Topology StatMech StatMech.Ising


/--
[plusState_spin_eq_magnetization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateSpinProfileLimit.lean)
-/
@[path]
private lemma plusState_spin_eq_magnetization_eq
  {d : Nat}
  {beta : Real}
  {x : Site d}
-- given
  (hbeta : 0 <= beta) :
-- imply
  (∫ omega, spin omega x ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) = magnetization d beta := by
-- proof
  apply StatMech.Ising.plusState_spin_eq_magnetization beta hbeta x

/--
[exists_plusMeasure_spin_profile_tendsto_magnetization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateSpinProfileLimit.lean)
-/
@[path]
private lemma exists_plusMeasure_spin_profile_tendsto_magnetization_eq
  {d : Nat}
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 <= beta) :
-- imply
  ∃ phi : Nat -> Nat, StrictMono phi ∧ forall x : Site d, Tendsto (fun n => ∫ omega, spin omega x ∂(plusMeasure d (phi n) beta 0 : Measure (ConfigSpace (Site d)))) atTop (nhds (magnetization d beta)) := by
-- proof
  apply StatMech.Ising.exists_plusMeasure_spin_profile_tendsto_magnetization d beta hbeta

/--
[integral_spin_eq_two_mul_real_spinUp_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateSpinProfileLimit.lean)
-/
@[path]
private lemma integral_spin_eq_two_mul_real_spinUp_sub_one_eq
  {d : Nat}
  {mu : ProbabilityMeasure (ConfigSpace (Site d))}
  {x : Site d} :
-- imply
  (∫ omega, spin omega x ∂(mu : Measure (ConfigSpace (Site d)))) = 2 * (mu : Measure (ConfigSpace (Site d))).real {omega | omega x = true} - 1 := by
-- proof
  apply StatMech.Ising.integral_spin_eq_two_mul_real_spinUp_sub_one mu x

/--
[plusMeasure_spin_full_tendsto_magnetization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateSpinProfileLimit.lean)
-/
@[path]
private lemma plusMeasure_spin_full_tendsto_magnetization_eq
  {d : Nat}
  {beta : Real}
  {x : Site d}
-- given
  (hbeta : 0 <= beta) :
-- imply
  Tendsto (fun n => ∫ omega, spin omega x ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) atTop (nhds (magnetization d beta)) := by
-- proof
  apply StatMech.Ising.plusMeasure_spin_full_tendsto_magnetization beta hbeta x

/--
[magnetization_le_plusMeasure_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateSpinProfileLimit.lean)
-/
@[path]
private lemma magnetization_le_plusMeasure_spin_eq
  {d : Nat}
  {beta : Real}
  {n : Nat}
  {x : Site d}
-- given
  (hbeta : 0 <= beta) :
-- imply
  magnetization d beta <= ∫ omega, spin omega x ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.magnetization_le_plusMeasure_spin beta hbeta n x


-- created on 2026-10-23
