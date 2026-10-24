import Mathlib

set_option autoImplicit false

noncomputable section

universe u

namespace AffineDilatation

variable {A : Type u} [CommRing A]

def gen (I : Ideal A) (a : A) : Set (Localization.Away a) :=
  (fun g : A => IsLocalization.mk' (Localization.Away a) g
    (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)) '' (I : Set A)

def subalgebra (I : Ideal A) (a : A) : Subalgebra A (Localization.Away a) :=
  Algebra.adjoin A (gen I a)

abbrev Ring (I : Ideal A) (a : A) : Type u :=
  ↥(subalgebra I a)

def divElem (I : Ideal A) (a : A) (g : A) (hg : g ∈ I) : Ring I a :=
  ⟨IsLocalization.mk' (Localization.Away a) g (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a),
    Algebra.subset_adjoin ⟨g, hg, rfl⟩⟩

@[simp]
theorem coe_divElem (I : Ideal A) (a : A) (g : A) (hg : g ∈ I) :
    ((divElem I a g hg : Ring I a) : Localization.Away a) =
      IsLocalization.mk' (Localization.Away a) g
        (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a) :=
  rfl

theorem coe_algebraMap (I : Ideal A) (a : A) (g : A) :
    ((algebraMap A (Ring I a) g : Ring I a) : Localization.Away a) =
      algebraMap A (Localization.Away a) g :=
  rfl

theorem algebraMap_mul_divElem (I : Ideal A) (a : A) (g : A) (hg : g ∈ I) :
    algebraMap A (Ring I a) a * divElem I a g hg = algebraMap A (Ring I a) g := by
  apply Subtype.ext
  change algebraMap A (Localization.Away a) a *
      IsLocalization.mk' (Localization.Away a) g
        (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a) =
    algebraMap A (Localization.Away a) g
  rw [mul_comm]
  exact IsLocalization.mk'_spec (Localization.Away a) g
    (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)

theorem mem_gen_iff (I : Ideal A) (a : A) (x : Localization.Away a) :
    x ∈ gen I a ↔ ∃ g ∈ I, IsLocalization.mk' (Localization.Away a) g
      (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a) = x :=
  Iff.rfl

theorem subalgebra_eq_adjoin (I : Ideal A) (a : A) :
    subalgebra I a = Algebra.adjoin A (gen I a) :=
  rfl

theorem gen_subset (I : Ideal A) (a : A) :
    gen I a ⊆ (subalgebra I a : Set (Localization.Away a)) :=
  Algebra.subset_adjoin

theorem divElem_mem (I : Ideal A) (a : A) (g : A) (hg : g ∈ I) :
    ((divElem I a g hg : Ring I a) : Localization.Away a) ∈ gen I a :=
  ⟨g, hg, rfl⟩

end AffineDilatation

end
