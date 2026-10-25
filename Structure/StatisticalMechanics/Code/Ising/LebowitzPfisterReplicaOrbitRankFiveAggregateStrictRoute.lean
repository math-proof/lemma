/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteTarget
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

structure LPReplicaAggregateRankFiveStrictRouteData
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (a : LPReplicaAggregateDecoratedSource G sites q) (k : I) where
  c : Copy (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
  d : Copy (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
  u : I
  v : I
  hc : c.1.1 = lpReplicaCurrentSeamEdge sites k
  hdK : d ∈ Finset.univ \ {c}
  hu : u = a.1 ∨ u = a.2.1 ∨ u = k
  hv : v = a.1 ∨ v = a.2.1 ∨ v = k
  huv : u ≠ v
  hfold : lpReplicaCurrentFoldedEdge G sites d.1 =
    s(Sum.inl (sites u), Sum.inl (sites v))
  hl : let l := lpReplicaThirdOfThree a.1 a.2.1 k u v
    l ≠ u ∧ l ≠ v ∧ (l = a.1 ∨ l = a.2.1 ∨ l = k)
  hdisc :
    let m := a.2.2.2.1.1.1
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m
        (Finset.univ \ {d}))
      (profileFlux (lpReplicaCurrentGraph G sites) m {d})
    let K' := lpReplicaPartialReflectCopiesRaw
      G sites m {d} (Finset.univ \ {c})
    ¬ connK (endsM (lpReplicaCurrentGraph G sites) target) K'
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1


end
end StatMech.Ising
