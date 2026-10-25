import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

namespace ModularCurve

variable {G : Type*} [Group G] {R : Type*} [CommRing R]
  {J : Type*} [AddCommGroup J] [Module R J] [DistribMulAction G J]

def MultiplicativeType (I : Subgroup G) (χ : G →* Rˣ) (W : Submodule R J) : Prop :=
  ∀ σ ∈ I, ∀ x ∈ W, σ • x = (χ σ : R) • x

def MultiplicativeTypeNat (I : Subgroup G) (n : G → ℕ) (W : AddSubgroup J) : Prop :=
  ∀ σ ∈ I, ∀ x ∈ W, σ • x = n σ • x

end ModularCurve
