import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteTarget
open StatMech StatMech.Ising


/--
[lpReplicaRowGate_canonicalizeRawPartialReflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteTarget.lean)
-/
@[path]
private lemma lpReplicaRowGate_canonicalizeRawPartialReflect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (rawTag : Copy (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) -> LPReplicaRowTag)
  (hraw : LPReplicaRowGate G sites (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) A B rawTag) :
-- imply
  LPReplicaRowGate G sites (lpReplicaPartialReflectProfile G sites m (profileFlux (lpReplicaCurrentGraph G sites) m P)) A B (lpReplicaTransportTag G sites (lpReplicaPartialReflectCanonicalRelabelEquiv G sites q m hm L P) rawTag) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_canonicalizeRawPartialReflect G sites q m hm L P rawTag A B hraw


-- created on 2026-10-23
