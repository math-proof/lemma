/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveRouting.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictIncidence


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplica_partialReflect_strictMatchingRoute_hasDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    {u v : I} (huv : u ≠ v)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (B : Finset (LPReplicaCurrentVertex V))
    (d : Copy (lpReplicaCurrentGraph G sites) m)
    (hdK : d ∈ K)
    (hunique : ∀ x ∈ B,
      ∃! e, e ∈ K ∧
        x ∈ (endsM (lpReplicaCurrentGraph G sites) m e).toFinset)
    (hreflectedSupport : ∀ x ∈
      endsM (lpReplicaCurrentGraph G sites) m d,
      lpReplicaCurrentReflect x ∈ B)
    (hfold : lpReplicaCurrentFoldedEdge G sites d.1 =
      s(Sum.inl (sites u), Sum.inl (sites v)))
    (hdisjoint : Disjoint
      (endsM (lpReplicaCurrentGraph G sites) m d).toFinset
      (Sym2.map lpReplicaCurrentReflect
        (endsM (lpReplicaCurrentGraph G sites) m d)).toFinset) :
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m
        (Finset.univ \ {d}))
      (profileFlux (lpReplicaCurrentGraph G sites) m {d})
    LPReplicaStrictPhysicalDoubleIncidenceRaw G sites target
      (lpReplicaPartialReflectCopiesRaw G sites m {d} K) := by
  classical
  dsimp only
  let target := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m
      (Finset.univ \ {d}))
    (profileFlux (lpReplicaCurrentGraph G sites) m {d})
  let R := lpReplicaPartialReflectCopyEquivRaw G sites m {d}
  let d' := R d
  let K' := lpReplicaPartialReflectCopiesRaw G sites m {d} K
  have hincidence :=
    lpReplica_partialReflect_strictMatchingRoute_doubleIncidence
      G sites m K B d hdK hunique hreflectedSupport hdisjoint
  change d' ∈ K' ∧
      ∀ x ∈ endsM (lpReplicaCurrentGraph G sites) target d',
        ∃ e' ∈ K', e' ≠ d' ∧
          x ∈ endsM (lpReplicaCurrentGraph G sites) target e' at hincidence
  have hd'edge : d'.1 = lpReplicaCurrentEdgeReflect G sites d.1 := by
    simpa only [d', R, Finset.mem_singleton, ↓reduceIte] using
      (lpReplicaPartialReflectCopyEquivRaw_edge G sites m {d} d)
  have hd'nondiag :
      ¬ (lpReplicaCurrentFoldedEdge G sites d'.1).IsDiag := by
    rw [hd'edge, lpReplicaCurrentFoldedEdge_reflect, hfold,
      Sym2.mk_isDiag_iff]
    exact fun h => hsite.ne huv (Sum.inl.inj h)
  exact ⟨d', hincidence.1, hd'nondiag, hincidence.2⟩


end
end StatMech.Ising
