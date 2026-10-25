/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSourceTrace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitProfileTransferGraph.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaDecoratedSourceRowGateData
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    {tag : Copy (lpReplicaCurrentGraph G sites) z.1.1.1 -> LPReplicaRowTag //
      LPReplicaRowGate G sites z.1.1.1 ∅
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) tag} := by
  let m := z.1.1.1
  let a := z.1.2.1.1
  let Sa := z.1.2.2.1.1
  let Sb := z.1.2.2.2.1
  let P0 := z.2.1.1
  have ha : a <= m := z.1.2.1.2
  have hSa := z.1.2.2.1.2
  have hSb := z.1.2.2.2.2
  have hP0 : profileFlux (lpReplicaCurrentGraph G sites) m P0 = a :=
    (Finset.mem_filter.mp z.2.1.2).2
  let tag := lpReplicaOrbitCollisionSplitTag G sites m a P0 hP0 Sa Sb
  have hgate0 := lpReplicaRowGate_orbitCollisionSplitTag
    G sites m a ha P0 hP0 Sa Sb ∅
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      hSa hSb
  have hfixed := lpReplicaCurrentReflect_offdiagSource G sites i j
  refine ⟨tag, ?_⟩
  simpa only [m, a, Sa, Sb, P0, tag, hfixed] using hgate0


noncomputable def lpReplicaDecoratedSourceSwappedRowGateData
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    {tag : Copy (lpReplicaCurrentGraph G sites) z.1.1.1 -> LPReplicaRowTag //
      LPReplicaRowGate G sites z.1.1.1
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) ∅ tag} := by
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  exact ⟨lpReplicaSwapRowsTag d.1,
    lpReplicaRowGate_swapRows G sites z.1.1.1 _ _ d.1 d.2⟩


noncomputable def lpReplicaDecoratedSourceCanonicalHalf
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    Finset (LPReplicaCurrentVertex V) :=
  let B :=
    lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  B ∩ StatMech.Sharpness.RandomCurrent.compOf
    (endsM (lpReplicaCurrentGraph G sites) z.1.1.1)
    (lpReplicaRowCopies G sites z.1.1.1 d.1 false)
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)


noncomputable def lpReplicaDecoratedSourceCanonicalHalfSelector
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    LPReplicaBalancedSelector G sites
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      (lpReplicaDecoratedSourceCanonicalHalf G sites i j q z) q := by
  let B :=
    lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  simpa only [lpReplicaDecoratedSourceCanonicalHalf, B, d] using
    lpReplicaBalancedSelectorOfComponentExchange G sites B q z.1.1.1
      d.1 z.1.1.2 d.2 z.2.2


end
end StatMech.Ising
