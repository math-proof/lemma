module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Structure.GroupCohomology_Selmer

@[expose] public section

set_option autoImplicit false

open CategoryTheory Module

universe u

namespace Representation

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

def twist (ρ : Representation k G V) (χ : G →* kˣ) : Representation k G V where
  toFun g := (χ g : k) • ρ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, Units.val_mul, mul_smul, smul_mul_assoc, mul_smul_comm]

lemma twist_apply (ρ : Representation k G V) (χ : G →* kˣ) (g : G) :
    ρ.twist χ g = (χ g : k) • ρ g := rfl

lemma twist_apply_apply (ρ : Representation k G V) (χ : G →* kˣ) (g : G) (v : V) :
    ρ.twist χ g v = (χ g : k) • ρ g v := rfl

@[simp]
lemma twist_one (ρ : Representation k G V) : ρ.twist 1 = ρ := by
  ext g v
  simp [twist_apply_apply]

end Representation

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

noncomputable abbrev twist (A : Rep k G) (χ : G →* kˣ) : Rep k G :=
  Rep.of (A.ρ.twist χ)

end Rep

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} [Fintype ι] {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ)


end groupCohomology
