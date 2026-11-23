module

public import Mathlib

@[expose] public section

set_option autoImplicit false

open scoped NumberField nonZeroDivisors

namespace JacobiSumStickelberger

section ModP

variable (p : ℕ) (M : Type*) [AddCommGroup M]

def nsmulRange : AddSubgroup M where
  carrier := Set.range fun x : M => p • x
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, smul_add p x y⟩
  zero_mem' := ⟨0, smul_zero p⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by simp⟩

abbrev ModP : Type _ := M ⧸ nsmulRange p M

def ModP.proj : M →+ ModP p M := QuotientAddGroup.mk' (nsmulRange p M)

variable {M} in

variable {M} in

def ModP.mapHom (f : M →+ M) : ModP p M →+ ModP p M :=
  QuotientAddGroup.map (nsmulRange p M) (nsmulRange p M) f (nsmulRange_le_comap p f)

variable {M} in
variable {M} in

noncomputable def ModP.mapEnd [NeZero p] (f : M →+ M) : Module.End (ZMod p) (ModP p M) :=
  (ModP.mapHom p f).toZModLinearMap p

end ModP

section ClassGroupCarrier

variable (p : ℕ) [NeZero p]
variable (R : Type*) [CommRing R] [IsDomain R]

abbrev ClGalModule : Type _ := ModP p (Additive (ClassGroup R))

noncomputable def clProj : Additive (ClassGroup R) →+ ClGalModule p R :=
  ModP.proj p (Additive (ClassGroup R))

omit [NeZero p] in
variable {R}

noncomputable def clEnd (g : R ≃+* R) : Module.End (ZMod p) (ClGalModule p R) :=
  ModP.mapEnd p (MonoidHom.toAdditive (ClassGroup.mulEquiv g).toMonoidHom)

end ClassGroupCarrier

end JacobiSumStickelberger

end
