import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.ZMod.Defs

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld.Mumford

variable {W : Type}

def vertexType (𝒯 : SimpleGraph W) (w₀ w : W) : ZMod 2 := (𝒯.dist w₀ w : ZMod 2)

theorem vertexType_apply (𝒯 : SimpleGraph W) (w₀ w : W) : vertexType 𝒯 w₀ w = (𝒯.dist w₀ w : ZMod 2) := rfl

@[simp] theorem vertexType_self (𝒯 : SimpleGraph W) (w₀ : W) : vertexType 𝒯 w₀ w₀ = 0 := by
  rw [vertexType, SimpleGraph.dist_self, Nat.cast_zero]

def typePreserving (G : Type) [Group G] [MulAction G W] (𝒯 : SimpleGraph W) (w₀ : W) : Subgroup G where
  carrier := {g | ∀ w : W, vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w}
  one_mem' := fun w => by rw [one_smul]
  mul_mem' {g h} hg hh := fun w => by rw [mul_smul, hg, hh]
  inv_mem' {g} hg := fun w => by rw [← hg (g⁻¹ • w), smul_inv_smul]

@[simp] theorem mem_typePreserving_iff {G : Type} [Group G] [MulAction G W] (𝒯 : SimpleGraph W) (w₀ : W) (g : G) :
    g ∈ typePreserving G 𝒯 w₀ ↔ ∀ w : W, vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w := Iff.rfl

end CerednikDrinfeld.Mumford

end
