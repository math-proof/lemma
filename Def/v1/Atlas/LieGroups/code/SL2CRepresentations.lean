/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2CRepresentations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part4
public import Theorem.Nat.basisHC.eq.SMul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Structure.v1.Atlas.LieGroups.code.SL2CRepresentations

@[expose] public section

noncomputable section

open Complex

open scoped Classical

attribute [instance] SL2C_UnitaryRep.instNACG
  SL2C_UnitaryRep.instIPS SL2C_UnitaryRep.instCS

def SL2C_UnitaryRep.IsIrreducible (ρ : SL2C_UnitaryRep) : Prop :=
  ∀ S : Submodule ℂ ρ.V, IsClosed (S : Set ρ.V) →
    (∀ g : SL2C, ∀ v ∈ S, (ρ.action g) v ∈ S) → S = ⊥ ∨ S = ⊤

def SL2C_UnitaryRep.IsUnitarilyEquiv (ρ₁ ρ₂ : SL2C_UnitaryRep) : Prop :=
  ∃ (T : ρ₁.V ≃ₗᵢ[ℂ] ρ₂.V), ∀ g : SL2C, ∀ v : ρ₁.V,
    T (ρ₁.action g v) = ρ₂.action g (T v)

def trivialSL2CRep : SL2C_UnitaryRep where
  V := ℂ
  action :=
    { toFun := fun _ => LinearIsometryEquiv.refl ℂ ℂ
      map_one' := rfl
      map_mul' := fun _ _ => by ext; simp }

end
