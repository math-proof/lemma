module

public import Mathlib

public section

set_option autoImplicit false

open scoped NumberField nonZeroDivisors

namespace JacobiSumStickelberger

section ModP

variable (p : ℕ) (M : Type*) [AddCommGroup M]


@[simp] public theorem mem_nsmulRange {x : M} : x ∈ nsmulRange p M ↔ ∃ y, p • y = x := Iff.rfl


public theorem nsmul_mem_nsmulRange (x : M) : p • x ∈ nsmulRange p M := ⟨x, rfl⟩


@[simp] public theorem ModP.proj_apply (x : M) : ModP.proj p M x = QuotientAddGroup.mk x := rfl


public theorem ModP.proj_surjective : Function.Surjective (ModP.proj p M) :=
  QuotientAddGroup.mk'_surjective _


public theorem ModP.proj_eq_zero_iff {x : M} : ModP.proj p M x = 0 ↔ ∃ y, p • y = x :=
  (QuotientAddGroup.eq_zero_iff x).trans (mem_nsmulRange p M)

variable {M} in


public theorem nsmulRange_le_comap (f : M →+ M) : nsmulRange p M ≤ (nsmulRange p M).comap f := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, (map_nsmul f p x).symm⟩

variable {M} in


@[simp] public theorem ModP.mapHom_proj (f : M →+ M) (x : M) :
    ModP.mapHom p f (ModP.proj p M x) = ModP.proj p M (f x) := rfl


@[simp] public theorem ModP.mapEnd_proj [NeZero p] (f : M →+ M) (x : M) :
    ModP.mapEnd p f (ModP.proj p M x) = ModP.proj p M (f x) := rfl

end ModP

section ClassGroupCarrier

variable (p : ℕ) [NeZero p]
variable (R : Type*) [CommRing R] [IsDomain R]


public theorem clProj_surjective : Function.Surjective (clProj p R) :=
  ModP.proj_surjective p (Additive (ClassGroup R))

variable {R}


@[simp] public theorem clEnd_clProj (g : R ≃+* R) (C : ClassGroup R) :
    clEnd p g (clProj p R (Additive.ofMul C)) =
      clProj p R (Additive.ofMul (ClassGroup.mulEquiv g C)) := rfl

end ClassGroupCarrier

end JacobiSumStickelberger
