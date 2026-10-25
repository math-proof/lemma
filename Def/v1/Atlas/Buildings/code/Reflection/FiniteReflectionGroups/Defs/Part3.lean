/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/FiniteReflectionGroups/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part4
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Finite.Basic
import Structure.v1.Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Defs
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace FiniteReflectionGroups

variable {Φ : RootSystem E}

/-- A root system is *reduced* if the only roots proportional to $α$ are $±α$. -/
def RootSystem.IsReduced (Φ : RootSystem E) : Prop :=
  ∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, (∃ c : ℝ, β = c • α) → β = α ∨ β = -α

/-- A root system is *crystallographic* if every pairing $⟨α, \check β⟩$ is an integer. -/
def RootSystem.IsCrystallographic (Φ : RootSystem E) : Prop :=
  ∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, ∃ n : ℤ, ⟪α, coroot β⟫_ℝ = ↑n

/-- The set of coroots $\{\check α : α ∈ Φ\}$. -/
def RootSystem.corootSet (Φ : RootSystem E) : Set E :=
  { v | ∃ α ∈ Φ.roots, v = coroot α }

/-- Positive roots relative to a separating linear functional $f$: those $α ∈ Φ$ with
$f(α) > 0$. -/
def RootSystem.positiveRootSet (Φ : RootSystem E) (f : E → ℝ) : Set E :=
  { α ∈ (Φ.roots : Set E) | f α > 0 }

/-- Negative roots relative to $f$: those $α ∈ Φ$ with $f(α) < 0$. -/
def RootSystem.negativeRootSet (Φ : RootSystem E) (f : E → ℝ) : Set E :=
  { α ∈ (Φ.roots : Set E) | f α < 0 }

/-- A positive root $α$ is *simple* relative to $f$ if it is not a sum of two positive
roots. -/
def RootSystem.IsSimpleRoot (Φ : RootSystem E) (f : E → ℝ) (α : E) : Prop :=
  α ∈ Φ.positiveRootSet f ∧
    ¬∃ (β γ : E), β ∈ Φ.positiveRootSet f ∧ γ ∈ Φ.positiveRootSet f ∧ α = β + γ

/-- The set of simple roots relative to a separating functional $f$. -/
def RootSystem.simpleRootSet (Φ : RootSystem E) (f : E → ℝ) : Set E :=
  { α : E | Φ.IsSimpleRoot f α }

end FiniteReflectionGroups
end
