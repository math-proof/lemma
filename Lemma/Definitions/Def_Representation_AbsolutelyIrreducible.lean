import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option autoImplicit false

section

open LinearMap
open scoped TensorProduct

namespace Representation

universe u

variable {R V G : Type*} [CommRing R] [AddCommMonoid V] [Module R V] [Group G]

noncomputable def baseChange (R' : Type*) [CommRing R'] [Algebra R R'] (ρ : Representation R G V)
    : Representation R' G (R' ⊗[R] V) where
  toFun g := LinearMap.baseChange R' (ρ g)
  map_one' := by aesop
  map_mul' := by aesop

scoped notation R' "⊗ᵣ'" ρ => baseChange R' ρ

variable {k : Type*} [Field k] {W : Type*} [AddCommMonoid W] [Module k W]

class IsAbsolutelyIrreducible (ρ : Representation k G W) : Prop where
  absolutelyIrreducible :
    ∀ k' : Type u, ∀ _ : Field k', ∀ _ : Algebra k k', IsIrreducible (k' ⊗ᵣ' ρ)

end Representation

end
