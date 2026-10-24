/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.ProjectionTheory.code.BorsukUlam
import Lemma.Real.Atlas.v1.ProjectionTheory.code.BorsukUlam

open MeasureTheory InnerProductSpace Set Filter Topology

namespace HamSandwich

noncomputable section

/-- The open half-space `{x : ⟨v, x⟩ < c} ⊆ ℝⁿ`. -/
def halfSpaceBelow (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ⟪v, x⟫_ℝ < c}

/-- The open half-space `{x : ⟨v, x⟩ > c} ⊆ ℝⁿ`. -/
def halfSpaceAbove (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ⟪v, x⟫_ℝ > c}

/-- A hyperplane with normal `v` and offset `c` *bisects* a set `A ⊆ ℝⁿ` if the two open
half-spaces it defines have equal Lebesgue measure when intersected with `A`. -/
def Bisects (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  volume (A ∩ halfSpaceBelow n v c) = volume (A ∩ halfSpaceAbove n v c)

/-- Given `θ ∈ ℝⁿ⁺¹` (a parameter on the unit sphere), `extractNormal` returns the first
`n` coordinates regarded as the normal vector of a hyperplane in `ℝⁿ`. -/
def extractNormal (n : ℕ) (θ : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => θ (Fin.castSucc i))

/-- Given `θ ∈ ℝⁿ⁺¹`, `extractOffset` returns its last coordinate, interpreted as the
constant `c` of an affine hyperplane `⟨v, x⟩ = c`. -/
def extractOffset (n : ℕ) (θ : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  θ (Fin.last n)

/-- The affine functional `x ↦ ⟨extractNormal θ, x⟩ - extractOffset θ` whose sign
determines the two sides of the hyperplane parametrised by `θ ∈ Sⁿ`. -/
def affineFunctional (n : ℕ) (θ : EuclideanSpace ℝ (Fin (n + 1)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪extractNormal n θ, x⟫_ℝ - extractOffset n θ
