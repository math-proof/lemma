import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCardinality.Part2
open Finset StatMech StatMech.Ising


/--
[lpReplicaRowFiberMass_eq_cardinalSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCardinality.lean)
-/
@[path]
private lemma lpReplicaRowFiberMass_eq_cardinalSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaRowFiberMass G sites beta J hf r A B m = ∑ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m}, (#(lpReplicaDisconnProfileFamily G sites A K.1) : Real) * (#(lpReplicaDisconnProfileFamily G sites B (lpReplicaReflectedResidual G sites m K.1)) : Real) * (weight (lpReplicaCurrentGraph G sites) beta (lpReplicaCurrentCoupling J hf r) (ofEdgeFun (lpReplicaCurrentGraph G sites) K.1) * weight (lpReplicaCurrentGraph G sites) beta (lpReplicaCurrentCoupling J hf r) (ofEdgeFun (lpReplicaCurrentGraph G sites) (lpReplicaReflectedResidual G sites m K.1))) := by
-- proof
  apply StatMech.Ising.lpReplicaRowFiberMass_eq_cardinalSum G sites beta J hf r A B m

/--
[lpReplicaProfileOrbitMass_eq_cardinalSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCardinality.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitMass_eq_cardinalSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaProfileOrbitMass G sites beta J hf r A B q = ∑ m : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // lpReplicaSymmetrizedProfile G sites p = q}, ∑ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m.1}, (#(lpReplicaDisconnProfileFamily G sites A K.1) : Real) * (#(lpReplicaDisconnProfileFamily G sites B (lpReplicaReflectedResidual G sites m.1 K.1)) : Real) * (weight (lpReplicaCurrentGraph G sites) beta (lpReplicaCurrentCoupling J hf r) (ofEdgeFun (lpReplicaCurrentGraph G sites) K.1) * weight (lpReplicaCurrentGraph G sites) beta (lpReplicaCurrentCoupling J hf r) (ofEdgeFun (lpReplicaCurrentGraph G sites) (lpReplicaReflectedResidual G sites m.1 K.1))) := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitMass_eq_cardinalSum G sites beta J hf r A B q

/--
[lpReplicaProfileOrbitMass_eq_sum_configurationWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCardinality.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitMass_eq_sum_configurationWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaProfileOrbitMass G sites beta J hf r A B q = ∑ x : LPReplicaOrbitConfiguration G sites A B q, lpReplicaOrbitConfigurationWeight G sites beta J hf r A B q x := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitMass_eq_sum_configurationWeight G sites beta J hf r A B q

/--
[lpReplicaProfileOrbitMass_le_add_of_weightedInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCardinality.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitMass_le_add_of_weightedInjection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B C D E F : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (move : LPReplicaOrbitConfiguration G sites A B q -> LPReplicaOrbitConfiguration G sites C D q ⊕ LPReplicaOrbitConfiguration G sites E F q)
  (hmove : Function.Injective move)
  (hweight : ∀ x, lpReplicaOrbitConfigurationWeight G sites beta J hf r A B q x = match move x with | .inl y => lpReplicaOrbitConfigurationWeight G sites beta J hf r C D q y | .inr y => lpReplicaOrbitConfigurationWeight G sites beta J hf r E F q y) :
-- imply
  lpReplicaProfileOrbitMass G sites beta J hf r A B q <= lpReplicaProfileOrbitMass G sites beta J hf r C D q + lpReplicaProfileOrbitMass G sites beta J hf r E F q := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitMass_le_add_of_weightedInjection G sites beta J hf r hbeta hJ hhf hr A B C D E F q move hmove hweight


-- created on 2026-10-23
