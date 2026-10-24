import Mathlib

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

@[simp] lemma mem_nsmulRange {x : M} : x ∈ nsmulRange p M ↔ ∃ y, p • y = x := Iff.rfl

lemma nsmul_mem_nsmulRange (x : M) : p • x ∈ nsmulRange p M := ⟨x, rfl⟩

abbrev ModP : Type _ := M ⧸ nsmulRange p M

instance instModuleZModModP [NeZero p] : Module (ZMod p) (ModP p M) :=
  QuotientAddGroup.zmodModule (nsmul_mem_nsmulRange p M)

def ModP.proj : M →+ ModP p M := QuotientAddGroup.mk' (nsmulRange p M)

@[simp] lemma ModP.proj_apply (x : M) : ModP.proj p M x = QuotientAddGroup.mk x := rfl

theorem ModP.proj_surjective : Function.Surjective (ModP.proj p M) :=
  QuotientAddGroup.mk'_surjective _

theorem ModP.proj_eq_zero_iff {x : M} : ModP.proj p M x = 0 ↔ ∃ y, p • y = x :=
  (QuotientAddGroup.eq_zero_iff x).trans (mem_nsmulRange p M)

variable {M} in

lemma nsmulRange_le_comap (f : M →+ M) : nsmulRange p M ≤ (nsmulRange p M).comap f := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, (map_nsmul f p x).symm⟩

variable {M} in

def ModP.mapHom (f : M →+ M) : ModP p M →+ ModP p M :=
  QuotientAddGroup.map (nsmulRange p M) (nsmulRange p M) f (nsmulRange_le_comap p f)

variable {M} in
@[simp] lemma ModP.mapHom_proj (f : M →+ M) (x : M) :
    ModP.mapHom p f (ModP.proj p M x) = ModP.proj p M (f x) := rfl

variable {M} in

noncomputable def ModP.mapEnd [NeZero p] (f : M →+ M) : Module.End (ZMod p) (ModP p M) :=
  (ModP.mapHom p f).toZModLinearMap p

variable {M} in
@[simp] lemma ModP.mapEnd_proj [NeZero p] (f : M →+ M) (x : M) :
    ModP.mapEnd p f (ModP.proj p M x) = ModP.proj p M (f x) := rfl

end ModP

section ClassGroupCarrier

variable (p : ℕ) [NeZero p]
variable (R : Type*) [CommRing R] [IsDomain R]

abbrev ClGalModule : Type _ := ModP p (Additive (ClassGroup R))

noncomputable def clProj : Additive (ClassGroup R) →+ ClGalModule p R :=
  ModP.proj p (Additive (ClassGroup R))

omit [NeZero p] in
theorem clProj_surjective : Function.Surjective (clProj p R) :=
  ModP.proj_surjective p (Additive (ClassGroup R))

variable {R}

noncomputable def clEnd (g : R ≃+* R) : Module.End (ZMod p) (ClGalModule p R) :=
  ModP.mapEnd p (MonoidHom.toAdditive (ClassGroup.mulEquiv g).toMonoidHom)

@[simp] lemma clEnd_clProj (g : R ≃+* R) (C : ClassGroup R) :
    clEnd p g (clProj p R (Additive.ofMul C)) =
      clProj p R (Additive.ofMul (ClassGroup.mulEquiv g C)) := rfl

end ClassGroupCarrier

end JacobiSumStickelberger
