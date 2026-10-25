import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.DobrushinStateProfileLimit
open MeasureTheory Filter Topology StatMech StatMech.Ising


/--
[interfaceState_isInfiniteVolumeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DobrushinStateProfileLimit.lean)
-/
@[path]
private lemma interfaceState_isInfiniteVolumeState_eq
  {d : Nat}
  {i : Fin d}
  {beta : Real} :
-- imply
  InfiniteVolumeState (fun n => interfaceMeasure i n beta) (interfaceState i beta) := by
-- proof
  apply StatMech.Ising.interfaceState_isInfiniteVolumeState i beta

/--
[exists_interfaceMeasure_spin_profile_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DobrushinStateProfileLimit.lean)
-/
@[path]
private lemma exists_interfaceMeasure_spin_profile_tendsto_eq
  {d : Nat}
  {i : Fin d}
  {beta : Real} :
-- imply
  ∃ phi : Nat -> Nat, StrictMono phi ∧ forall x : Site d, Tendsto (fun n => ∫ omega, spin omega x ∂(interfaceMeasure i (phi n) beta : Measure (ConfigSpace (Site d)))) atTop (nhds (∫ omega, spin omega x ∂(interfaceState i beta : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.Ising.exists_interfaceMeasure_spin_profile_tendsto i beta

/--
[exists_common_plus_interface_spin_profile_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DobrushinStateProfileLimit.lean)
-/
@[path]
private lemma exists_common_plus_interface_spin_profile_tendsto_eq
  {d : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (hbeta : 0 <= beta) :
-- imply
  ∃ phi : Nat -> Nat, StrictMono phi ∧ forall x : Site d, (Tendsto (fun n => ∫ omega, spin omega x ∂(plusMeasure d (phi n) beta 0 : Measure (ConfigSpace (Site d)))) atTop (nhds (magnetization d beta))) ∧ (Tendsto (fun n => ∫ omega, spin omega x ∂(interfaceMeasure i (phi n) beta : Measure (ConfigSpace (Site d)))) atTop (nhds (∫ omega, spin omega x ∂(interfaceState i beta : Measure (ConfigSpace (Site d)))))) := by
-- proof
  apply StatMech.Ising.exists_common_plus_interface_spin_profile_tendsto i beta hbeta


-- created on 2026-10-23
