import Lemma.CohCarrier.Inst
import Abbrev.CohCarrier_HeckeDiamondRing

set_option autoImplicit false

noncomputable section

namespace CohCarrier

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (H' : Subgroup (ZMod M)ˣ)
  (A : Type) [CommRing A]

def heckeTFamily : GoodPrime M S → Module.End A (H1 M H A) :=
  fun ℓ => haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩; heckeTL M H A ℓ.1

theorem heckeTFamily_apply (ℓ : GoodPrime M S) (φ : H1 M H A) :
    heckeTFamily M H S A ℓ φ = (haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩; heckeT M H ℓ.1 A φ) := rfl

variable [NeZero M]

def heckeDiamondGens : Set (Module.End A (H1 M H A)) :=
  Set.range (heckeTFamily M H S A) ∪ Set.range (fun u : H' => diamondL M H A (u : (ZMod M)ˣ))

theorem heckeTL_mem_heckeDiamondGens (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) :
    (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeTL M H A ℓ) ∈ heckeDiamondGens M H S H' A :=
  Or.inl ⟨⟨ℓ, hℓ, hℓS, hℓM⟩, rfl⟩

theorem diamondL_mem_heckeDiamondGens (u : (ZMod M)ˣ) (hu : u ∈ H') :
    diamondL M H A u ∈ heckeDiamondGens M H S H' A :=
  Or.inr ⟨⟨u, hu⟩, rfl⟩

def heckeDiamondRing : Subalgebra ℤ (Module.End A (H1 M H A)) :=
  Algebra.adjoin ℤ (heckeDiamondGens M H S H' A)

namespace heckeDiamondRing

def T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) : ↥(heckeDiamondRing M H S H' A) :=
  ⟨(haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeTL M H A ℓ),
    Algebra.subset_adjoin (heckeTL_mem_heckeDiamondGens M H S H' A ℓ hℓ hℓS hℓM)⟩

@[simp] theorem coe_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) :
    ((T M H S H' A ℓ hℓ hℓS hℓM : ↥(heckeDiamondRing M H S H' A)) : Module.End A (H1 M H A)) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeTL M H A ℓ) := rfl

def diamond (u : (ZMod M)ˣ) (hu : u ∈ H') : ↥(heckeDiamondRing M H S H' A) :=
  ⟨diamondL M H A u, Algebra.subset_adjoin (diamondL_mem_heckeDiamondGens M H S H' A u hu)⟩

@[simp] theorem coe_diamond (u : (ZMod M)ˣ) (hu : u ∈ H') :
    ((diamond M H S H' A u hu : ↥(heckeDiamondRing M H S H' A)) : Module.End A (H1 M H A)) =
      diamondL M H A u := rfl

end heckeDiamondRing

end CohCarrier

end
