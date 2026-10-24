import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitWeight
open Finset StatMech StatMech.Ising


/--
[lpReplica_factorialPower_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitWeight.lean)
-/
@[path]
private lemma lpReplica_factorialPower_pair_eq
  [Fintype V]
  [DecidableEq V]
  {X : Real}
  {a b : Nat} :
-- imply
  X ^ a / Nat.factorial a * (X ^ b / Nat.factorial b) = X ^ (a + b) / Nat.factorial (a + b) * (Nat.choose (a + b) a : Real) := by
-- proof
  apply StatMech.Ising.lpReplica_factorialPower_pair X a b

/--
[lpReplicaWeight_eq_orbitMultiplicity_mul_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitWeight.lean)
-/
@[path]
private lemma lpReplicaWeight_eq_orbitMultiplicity_mul_base_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  weight (lpReplicaCurrentGraph G sites) beta (lpReplicaCurrentCoupling J hf r) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) = (lpReplicaProfileOrbitMultiplicity G sites q m : Real) * lpReplicaProfileOrbitBaseWeight G sites beta J hf r q := by
-- proof
  apply StatMech.Ising.lpReplicaWeight_eq_orbitMultiplicity_mul_base G sites beta J hf r q m hm


-- created on 2026-10-23
