/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/ShortestAugPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.ResidualGraph.Part2
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.ResidualGraph
open Finset BigOperators


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

def dirPathLengths (adj : V → V → Prop) (s t : V) : Set ℕ∞ :=
  { n : ℕ∞ | ∃ (k : ℕ) (p : List V), IsDirectedPath adj s t p ∧
    p.length = k + 1 ∧ n = ↑k }

noncomputable def dirDist (adj : V → V → Prop) (s t : V) : ℕ∞ :=
  sInf (dirPathLengths adj s t)

noncomputable def residualDist (N : FlowNetwork V) (fl : STFlow N) : ℕ∞ :=
  dirDist (resAdj N fl) N.s N.t

def EdgeOnPath (path : List V) (u v : V) : Prop :=
  ∃ i : ℕ, path[i]? = some u ∧ path[i + 1]? = some v

def IsShortestAugmentingPath (N : FlowNetwork V) (fl : STFlow N)
    (p : List V) : Prop :=
  IsAugmentingPath N fl p ∧
  (↑(p.length - 1) : ℕ∞) = residualDist N fl

def IsShortestPathAugmentation (N : FlowNetwork V) (fl fl' : STFlow N) : Prop :=
  ∃ p : List V,
    IsShortestAugmentingPath N fl p ∧
    (∑ v : V, fl'.f N.s v - ∑ v : V, fl'.f v N.s) >
    (∑ v : V, fl.f N.s v - ∑ v : V, fl.f v N.s) ∧
    (∀ u v, ¬ EdgeOnPath p u v → ¬ EdgeOnPath p v u → fl'.f u v = fl.f u v) ∧
    (∀ (q : List V) (hq : IsShortestAugmentingPath N fl q) (u v : V),
      EdgeOnPath q u v → resCap N fl u v = pathBottleneck N fl q hq.1.1 →
      ¬ resAdj N fl' u v)

end NetworkFlow
