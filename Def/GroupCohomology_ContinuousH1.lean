import Mathlib
import Lemma.GroupCohomology.ContinuousH2
import Lemma.GroupCohomology.ContinuousH2Map

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
  (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

section carriers

variable (M : Rep k G)

def levelCocycles₁ : Submodule k (cocycles₁ M) :=
  (levelCochains₁ r M).comap (cocycles₁ M).subtype


def continuousH1 : Submodule k (H1 M) :=
  (levelCocycles₁ r M).map (H1π M).hom

end carriers


section delta

variable {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)

open Classical in

def preimageFun (b : B) : A :=
  if h : ∃ a : A, φ.hom a = b then h.choose else 0


variable (hψ : Function.Surjective ψ.hom)

def deltaCochain₀ (c : C) : G → A :=
  fun g => preimageFun φ ((d₀₁ B).hom (Function.surjInv hψ c) g)

def deltaCochain₁ (c : G → C) : G × G → A :=
  fun p => preimageFun φ ((d₁₂ B).hom (Function.surjInv hψ ∘ c) p)

end delta

end groupCohomology

end
