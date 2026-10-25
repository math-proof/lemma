/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorEdgecopyBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorProfileCount.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFourReplicaCore
import Abbrev.StatisticalMechanics.Code.FrontierA.GrahamFourColorEdgecopyBridge
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def grahamFourSplitMultiplicityNat
    (total : G.edgeFinset -> Nat) (s : GrahamFourSplit G total) : Nat :=
  ∏ e : G.edgeFinset,
    (total e).choose (s.1.1 e) *
      (total e - s.1.1 e).choose (s.1.2.1 e) *
      (total e - s.1.1 e - s.1.2.1 e).choose (s.1.2.2 e)


noncomputable def grahamFourColorToSplit
    (total : G.edgeFinset -> Nat)
    (q : GrahamFourColoring (Copy G total)) : GrahamFourSplit G total :=
  if hq : q.IsPartition Finset.univ then
    ⟨(profileFlux G total q.color1,
      profileFlux G total q.color2,
      profileFlux G total q.color3),
      grahamFourColor_profile_sum_le G total q hq⟩
  else
    ⟨((fun _ => 0), (fun _ => 0), (fun _ => 0)), fun e => by simp⟩

end StatMech.FrontierA
