import Mathlib

set_option autoImplicit false
noncomputable section
open scoped TensorProduct

namespace FreyPackage.ModMCarrier

section LatticeRed
variable (k : Type*) [Field k] {W W' : Type*} [AddCommGroup W] [AddCommGroup W']
  [Module ℂ W] [Module ℂ W'] (L : Submodule ℤ W) (L' : Submodule ℤ W')

abbrev latticeRed : Type _ := k ⊗[ℤ] ↥L

def latticeRed.mk : ↥L →ₗ[ℤ] latticeRed k L := (TensorProduct.mk ℤ k (↥L)) 1

@[simp] lemma latticeRed.mk_eq_tmul (x : ↥L) : latticeRed.mk k L x = (1 : k) ⊗ₜ[ℤ] x := rfl

def latticeRestrictMap (g : W →ₗ[ℂ] W') (hg : ∀ x ∈ L, g x ∈ L') : ↥L →ₗ[ℤ] ↥L' where
  toFun x := ⟨g x, hg x x.2⟩
  map_add' x y := by simp [Subtype.ext_iff]
  map_smul' m x := by simp [Subtype.ext_iff, ← Int.cast_smul_eq_zsmul ℂ]

def latticeRed.mapOf (g : W →ₗ[ℂ] W') (hg : ∀ x ∈ L, g x ∈ L') :
    latticeRed k L →ₗ[k] latticeRed k L' :=
  LinearMap.baseChange k (latticeRestrictMap L L' g hg)

lemma latticeRed.mapOf_mk (g : W →ₗ[ℂ] W') (hg : ∀ x ∈ L, g x ∈ L') (x : ↥L) :
    latticeRed.mapOf k L L' g hg (latticeRed.mk k L x)
      = latticeRed.mk k L' ⟨g x, hg x x.2⟩ := rfl

end LatticeRed

end FreyPackage.ModMCarrier
