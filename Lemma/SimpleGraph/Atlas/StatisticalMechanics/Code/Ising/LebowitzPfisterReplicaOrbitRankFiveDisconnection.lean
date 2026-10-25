import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveDisconnection
open StatMech StatMech.Ising


/--
[lpReplicaPartialReflectCopiesRaw_sdiff_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveDisconnection.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_sdiff_singleton_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {d c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  let R := lpReplicaPartialReflectCopyEquivRaw G sites m {d} lpReplicaPartialReflectCopiesRaw G sites m {d} (Finset.univ \ {c}) = Finset.univ \ {R c} := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_sdiff_singleton G sites m d c

/--
[lpReplica_partialReflect_strictMatchingRoute_ghost_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveDisconnection.lean)
-/
@[path]
private lemma lpReplica_partialReflect_strictMatchingRoute_ghost_disconnected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {B : Finset (LPReplicaCurrentVertex V)}
  {d : Copy (lpReplicaCurrentGraph G sites) m}
  {u v : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hdK : d ∈ K)
  (hsupport : K.biUnion (fun e => (endsM (lpReplicaCurrentGraph G sites) m e).toFinset) = B)
  (hunique : ∀ x ∈ B, ∃! e, e ∈ K ∧ x ∈ (endsM (lpReplicaCurrentGraph G sites) m e).toFinset)
  (hg0B : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ B)
  (hg1B : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ B)
  (huv : u ≠ v)
  (hfold : lpReplicaCurrentFoldedEdge G sites d.1 = s(Sum.inl (sites u), Sum.inl (sites v))) :
-- imply
  let target := lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ {d})) (profileFlux (lpReplicaCurrentGraph G sites) m {d}) let K' := lpReplicaPartialReflectCopiesRaw G sites m {d} K ¬ connK (endsM (lpReplicaCurrentGraph G sites) target) K' lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplica_partialReflect_strictMatchingRoute_ghost_disconnected G sites hsite m K B d hdK hsupport hunique hg0B hg1B huv hfold


-- created on 2026-10-23
