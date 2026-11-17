/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section12.Part2
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Normed.Module.Convex
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section13
open Finset BigOperators Set Metric

namespace AlgebraicTopologyI

/-- Inductive predicate `IsSubdivSimplex v τ` characterising the vertex
sets `τ ⊆ E` of simplices arising in the barycentric subdivision of the
affine simplex with vertices `v`. The base case is a single point; the
cone step adjoins the barycenter of `v` to a face subdivision. -/
public inductive IsSubdivSimplex : {n : ℕ} → (Fin (n + 1) → E) → Set E → Prop where
  | point (v : Fin 1 → E) : IsSubdivSimplex v {v 0}
  | cone {n : ℕ} (v : Fin (n + 2) → E) (k : Fin (n + 2)) (τ : Set E)
      (hτ : IsSubdivSimplex (v ∘ Fin.succAbove k) τ) :
      IsSubdivSimplex v (insert (barycenter (n + 1) v) τ)

end AlgebraicTopologyI
