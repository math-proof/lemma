/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/GKModule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
import Lemma.Complex.IsStronglyContinuousToMonoidHom
import Lemma.Complex.IsKFinite0
import Def.v1.Atlas.LieGroups.code.KFinite.Part3
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Structure.v1.Atlas.LieGroups.code.GKModule


noncomputable section

namespace GKModule

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]

variable {K : Type*} [Group K]

variable {𝔨 : LieSubalgebra ℂ 𝔤}

variable {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]

def IsIrreducibleGKModule (M : GKModule 𝔤 K 𝔨 Ad V) : Prop :=
  ∀ (W : Submodule ℂ V), M.IsSubmodule W → W = ⊥ ∨ W = ⊤

def IsKInvariant (M : GKModule 𝔤 K 𝔨 Ad V) (W : Submodule ℂ V) : Prop :=
  ∀ (k : K) (v : V), v ∈ W → M.σ k v ∈ W

def IsKIrreducible (M : GKModule 𝔤 K 𝔨 Ad V) (W : Submodule ℂ V) : Prop :=
  M.IsKInvariant W ∧
  ∀ (U : Submodule ℂ V), U ≤ W → M.IsKInvariant U → U = ⊥ ∨ U = W

def AreKIsomorphic (M : GKModule 𝔤 K 𝔨 Ad V)
    (W₁ W₂ : Submodule ℂ V)
    (h₁ : M.IsKInvariant W₁) (h₂ : M.IsKInvariant W₂) : Prop :=
  ∃ (f : W₁ ≃ₗ[ℂ] W₂), ∀ (k : K) (v : W₁),
    f ⟨M.σ k ↑v, h₁ k ↑v v.2⟩ = ⟨M.σ k ↑(f v), h₂ k ↑(f v) (f v).2⟩

def KIsotypicComponent (M : GKModule 𝔤 K 𝔨 Ad V)
    (W₀ : Submodule ℂ V) (hW₀ : M.IsKIrreducible W₀) : Submodule ℂ V :=
  sSup { W : Submodule ℂ V |
    ∃ (hIrr : M.IsKIrreducible W),
      M.AreKIsomorphic W W₀ hIrr.1 hW₀.1 }

def IsAdmissible (M : GKModule 𝔤 K 𝔨 Ad V) : Prop :=
  ∀ (W₀ : Submodule ℂ V) (hW₀ : M.IsKIrreducible W₀),
    FiniteDimensional ℂ (M.KIsotypicComponent W₀ hW₀)

end GKModule
end
