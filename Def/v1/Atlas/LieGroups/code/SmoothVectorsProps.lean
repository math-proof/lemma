/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SmoothVectorsProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.SmoothVectors
import Def.v1.Atlas.LieGroups.code.KFinite.Part3
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Geometry.Manifold.BumpFunction


section GStable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I ⊤ G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

end GStable

noncomputable section

open scoped Manifold

open MeasureTheory

namespace ContinuousRep

section Subspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {H : Type*} [TopologicalSpace H]

variable (I : ModelWithCorners ℝ E H)

variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]

variable [MeasureSpace G]

variable [LieGroup I ⊤ G]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

def repOfFunction (π : ContinuousRep G F) (f : G → ℂ) (v : F) : F :=
  ∫ g, (f g) • ((π.toMonoidHom g) v)

def IsSmoothCompactlySupportedFunction (f : G → ℂ) : Prop :=
  ContMDiff I 𝓘(ℝ, ℂ) (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f

def gardingSubspace (π : ContinuousRep G F) : Submodule ℂ F :=
  Submodule.span ℂ
    { w : F | ∃ (f : G → ℂ) (v : F),
        IsSmoothCompactlySupportedFunction I f ∧ w = π.repOfFunction f v }

def leftInvariantDeriv (lieExp : E → G) (X : E) (f : G → ℂ) (g : G) : ℂ :=
  deriv (fun t : ℝ => f (g * lieExp (t • X))) 0

end Subspace
end ContinuousRep
end
