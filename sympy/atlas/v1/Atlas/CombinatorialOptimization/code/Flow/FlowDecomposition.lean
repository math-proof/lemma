/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/FlowDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Flow.FlowCutBound
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowCutBound

open Finset BigOperators Classical

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def flowSupport (N : FlowNetwork V) (fl : STFlow N) : Finset (V × V) :=
  Finset.univ.filter (fun e => fl.f e.1 e.2 > 0)

structure FlowPath (N : FlowNetwork V) where
  vertices : List V
  nonempty : vertices ≠ []
  starts_at_s : vertices.head nonempty = N.s
  ends_at_t : vertices.getLast nonempty = N.t
  length_ge_two : vertices.length ≥ 2
  nodup : vertices.Nodup

def FlowPath.edges {N : FlowNetwork V} (p : FlowPath N) : List (V × V) :=
  p.vertices.zip p.vertices.tail

def FlowPath.mem_edges {N : FlowNetwork V} (p : FlowPath N) (u v : V) : Prop :=
  (u, v) ∈ p.edges

instance FlowPath.decidable_mem_edges {N : FlowNetwork V} (p : FlowPath N) (u v : V) :
    Decidable (p.mem_edges u v) := by
  unfold mem_edges edges; exact inferInstance

structure FlowDecomposition (N : FlowNetwork V) (fl : STFlow N) where
  f' : STFlow N
  same_value : flowValue N f' = flowValue N fl
  support_sub : flowSupport N f' ⊆ flowSupport N fl
  k : ℕ
  paths : Fin k → FlowPath N
  weights : Fin k → ℝ
  weights_pos : ∀ i, 0 < weights i
  flow_eq : ∀ u v, f'.f u v =
    ∑ i : Fin k, if (paths i).mem_edges u v then weights i else 0
  k_le_support : k ≤ (flowSupport N fl).card

def reachableInSupport (N : FlowNetwork V) (fl : STFlow N) (u v : V) : Prop :=
  Relation.ReflTransGen (fun a b => fl.f a b > 0) u v

noncomputable def reachableSet (N : FlowNetwork V) (fl : STFlow N) : Finset V :=
  Finset.univ.filter (fun v => reachableInSupport N fl N.s v)
