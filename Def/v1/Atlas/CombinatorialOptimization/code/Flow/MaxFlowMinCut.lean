/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowCutBound.Part2
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowCutBound
open Finset BigOperators Classical


noncomputable section

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

def resCap' (N : FlowNetwork V) (fl : STFlow N) (u v : V) : ℝ :=
  N.cap u v - fl.f u v + fl.f v u

def resAdj' (N : FlowNetwork V) (fl : STFlow N) (u v : V) : Prop :=
  resCap' N fl u v > 0

def ResReachable (N : FlowNetwork V) (fl : STFlow N) (v : V) : Prop :=
  Relation.ReflTransGen (resAdj' N fl) N.s v

def NoAugmentingPath (N : FlowNetwork V) (fl : STFlow N) : Prop :=
  ¬ ResReachable N fl N.t

def resReachableSet (N : FlowNetwork V) (fl : STFlow N) : Finset V :=
  Finset.univ.filter (fun v => ResReachable N fl v)

end NetworkFlow
end
