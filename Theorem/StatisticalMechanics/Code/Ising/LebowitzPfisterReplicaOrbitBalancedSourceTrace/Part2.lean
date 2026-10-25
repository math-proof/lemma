/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSourceTrace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitProfileTransferGraph.Part4
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaDecoratedSourceCanonicalHalf_missingSource
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    let X := lpReplicaDecoratedSourceCanonicalHalf G sites i j q z
    ((Si ∆ Sj ∆ T) ∆ Si =
        X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∨
      ((Si ∆ Sj ∆ T) ∆ Sj =
        X ∆ X.map lpReplicaCurrentReflect.toEmbedding) := by
  dsimp only
  let B :=
    lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  let K := lpReplicaRowCopies G sites z.1.1.1 d.1 false
  have hrows := lpReplicaRowGate_rowSources G sites z.1.1.1 B ∅ d.1 d.2
  have h := lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect_ghost1
    G sites hsite hij z.1.1.1 K hrows.1 d.2.2.2.1
  simpa only [B, d, K, lpReplicaDecoratedSourceCanonicalHalf] using h


end
end StatMech.Ising
