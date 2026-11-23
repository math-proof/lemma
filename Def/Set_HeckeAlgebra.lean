module

public import Mathlib
public import Instance.AbstractHeckeOperator
public import Structure.LocalLanglands_HeckePair

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
open Function MulAction


namespace HeckePair

noncomputable section

variable {G : Type*} [Group G] (U : Subgroup G)
variable (R₀ : Type*) [CommRing R₀]

variable {U R₀} in
variable {U R₀} in
variable {U R₀} in
def heckeSubmodule : Submodule R₀ (G → R₀) where
  carrier := {f | IsHeckeFun (U := U) f}
  add_mem' hf hg := hf.add hg
  zero_mem' := IsHeckeFun.zero
  smul_mem' r _ hf := hf.smul r

abbrev HeckeAlgebra := heckeSubmodule U R₀

variable {U R₀}

def convTerm (f₁ f₂ : HeckeAlgebra U R₀) (x : G) : G ⧸ U → R₀ :=
  Quotient.lift (fun y => (f₁ : G → R₀) y * (f₂ : G → R₀) (y⁻¹ * x)) <| by
    intro a b hab
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ U, a * u = b :=
      ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab, by group⟩
    rw [apply_mul_right f₁ hu, mul_inv_rev, mul_assoc, apply_left_mul f₂ (inv_mem hu)]

def conv (f₁ f₂ : HeckeAlgebra U R₀) (x : G) : R₀ :=
  ∑ᶠ c : G ⧸ U, convTerm f₁ f₂ x c

def heckeMul (f₁ f₂ : HeckeAlgebra U R₀) : HeckeAlgebra U R₀ :=
  ⟨conv f₁ f₂, isHeckeFun_conv f₁ f₂⟩

variable (U R₀) in
def heckeOne : HeckeAlgebra U R₀ :=
  ⟨Set.indicator (U : Set G) 1, by
    refine ⟨fun u hu x => ?_, fun u hu x => ?_, ?_⟩
    · by_cases hx : x ∈ U
      · simp only [Set.indicator_of_mem (mul_mem hu hx : u * x ∈ U),
          Set.indicator_of_mem hx, Pi.one_apply]
      · rw [Set.indicator_of_notMem (fun h => hx (by simpa using mul_mem (inv_mem hu) h)),
          Set.indicator_of_notMem hx]
    · by_cases hx : x ∈ U
      · simp only [Set.indicator_of_mem (mul_mem hx hu : x * u ∈ U),
          Set.indicator_of_mem hx, Pi.one_apply]
      · rw [Set.indicator_of_notMem (fun h => hx (by simpa using mul_mem h (inv_mem hu))),
          Set.indicator_of_notMem hx]
    · refine (Set.finite_singleton (QuotientGroup.mk (1 : G))).subset ?_
      rintro _ ⟨y, hy, rfl⟩
      have hyU : y ∈ U := by
        by_contra hyU
        exact hy (Set.indicator_of_notMem hyU 1)
      exact Set.mem_singleton_iff.mpr (QuotientGroup.eq.mpr (by simpa using inv_mem hyU))⟩

end
end HeckePair

end
