import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaAggregateSwitching
open Finset StatMech StatMech.Ising


/--
[lpReplicaMatchingDisconnTwoOffDiag_eq_sum_toggledMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaAggregateSwitching.lean)
-/
@[path]
private lemma lpReplicaMatchingDisconnTwoOffDiag_eq_sum_toggledMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (J : Sym2 (LPReplicaCurrentVertex V) -> Real) :
-- imply
  lpMatchingDisconnTwoOffDiag (lpReplicaCurrentGraph G sites) beta J (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 = ∑ i : I, ∑ j : I, lpReplicaOffdiagToggledMass G sites hsite beta J i j := by
-- proof
  apply StatMech.Ising.lpReplicaMatchingDisconnTwoOffDiag_eq_sum_toggledMass G sites hsite beta J

/--
[lpReplicaMatchingDisconnTwo_eq_sum_toggledMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaAggregateSwitching.lean)
-/
@[path]
private lemma lpReplicaMatchingDisconnTwo_eq_sum_toggledMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (J : Sym2 (LPReplicaCurrentVertex V) -> Real) :
-- imply
  lpMatchingDisconnTwo (lpReplicaCurrentGraph G sites) beta J (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 = ∑ i : I, ∑ j : I, lpReplicaOffdiagToggledMass G sites hsite beta J i j := by
-- proof
  apply StatMech.Ising.lpReplicaMatchingDisconnTwo_eq_sum_toggledMass G sites hsite beta J


-- created on 2026-10-23
