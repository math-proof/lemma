/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section12
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section12
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Module.Convex

open Finset BigOperators Set Metric

namespace AlgebraicTopologyI

/-- The barycenter of `n + 1` points `v 0, …, v n` in a real normed space:
the average `(n + 1)⁻¹ · Σ v i`. -/
def barycenter (n : ℕ) (v : Fin (n + 1) → E) : E :=
  (↑(n + 1) : ℝ)⁻¹ • ∑ i : Fin (n + 1), v i

/-- Inductive predicate `IsSubdivSimplex v τ` characterising the vertex
sets `τ ⊆ E` of simplices arising in the barycentric subdivision of the
affine simplex with vertices `v`. The base case is a single point; the
cone step adjoins the barycenter of `v` to a face subdivision. -/
inductive IsSubdivSimplex : {n : ℕ} → (Fin (n + 1) → E) → Set E → Prop where
  | point (v : Fin 1 → E) : IsSubdivSimplex v {v 0}
  | cone {n : ℕ} (v : Fin (n + 2) → E) (k : Fin (n + 2)) (τ : Set E)
      (hτ : IsSubdivSimplex (v ∘ Fin.succAbove k) τ) :
      IsSubdivSimplex v (insert (barycenter (n + 1) v) τ)

/-- The `k`-fold composition of a chain-complex endomorphism `f : C ⟶ C`,
i.e. `f^k`. Used to express iterates of the subdivision operator
`$^k : S_*(X) → S_*(X)` from Lemma 13.4. -/
def endoPow {C : ChainComplex AddCommGrpCat ℕ}
    (f : C ⟶ C) : ℕ → (C ⟶ C)
  | 0 => 𝟙 C
  | n + 1 => f ≫ endoPow f n

/-- The `0`-th iterate of `f` is the identity. -/
@[simp]
theorem endoPow_zero
    {C : ChainComplex AddCommGrpCat ℕ} (f : C ⟶ C) :
    endoPow f 0 = 𝟙 C := rfl

/-- Lemma 13.4 (chain-level witness). For every `k`, the `k`-fold iterate
`$^k` of the subdivision operator is chain-homotopic to the identity on
`S_*(X)`. The witness is built by induction on `k`, composing the one-step
subdivision chain homotopy with the previous iterate. -/
def iteratedSubdivisionHomotopy (X : TopCat.{0}) (k : ℕ) :
    Homotopy
      (endoPow (subdivisionOperator.app X) k)
      (𝟙 (singularChainFunctorZ.obj X)) := by
  induction k with
  | zero => exact Homotopy.ofEq (endoPow_zero _)
  | succ k IH =>
    have H := subdivisionChainHomotopy X
    have h1 := H.compRight (endoPow (subdivisionOperator.app X) k)
    have h2 :
        (𝟙 (singularChainFunctorZ.obj X)) ≫
          endoPow (subdivisionOperator.app X) k =
        endoPow (subdivisionOperator.app X) k :=
      Category.id_comp _
    exact h1.trans ((Homotopy.ofEq h2).trans IH)
