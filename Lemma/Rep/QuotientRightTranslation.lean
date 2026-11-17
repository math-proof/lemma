import Mathlib
import Lemma.Rep.Selmer
import Abbrev.Rep_QuotientRightTranslation
import Lemma.Ideal.Mathlib430

set_option autoImplicit false

open CategoryTheory

namespace Rep

universe u

variable {k : Type u} [CommRing k] {G : Type u} [Group G] (Λ : Subgroup G) [Λ.Normal]

theorem smul_quotient_eq_mul (g : G) (q : G ⧸ Λ) : g • q = (g : G ⧸ Λ) * q := by
  induction q using QuotientGroup.induction_on with
  | H a => rfl

@[simp] theorem quotientRightTranslation_hom_single (c q : G ⧸ Λ) (a : k) :
    (quotientRightTranslation (k := k) Λ c).hom (Finsupp.single q a) = Finsupp.single (q * c⁻¹) a := by
  show Finsupp.lmapDomain k k (· * c⁻¹) (Finsupp.single q a) = _
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem quotientRightTranslation_hom_apply (c : G ⧸ Λ) (x : G ⧸ Λ →₀ k) :
    (quotientRightTranslation (k := k) Λ c).hom x = Finsupp.mapDomain (· * c⁻¹) x := rfl

theorem quotientRightTranslation_one : quotientRightTranslation (k := k) Λ 1 = 𝟙 _ := by
  apply Rep.hom_ext; refine DFunLike.ext _ _ fun x => ?_
  show Finsupp.mapDomain (· * (1 : G ⧸ Λ)⁻¹) x = x
  simp only [inv_one, mul_one]
  exact Finsupp.mapDomain_id

theorem quotientRightTranslation_mul (c c' : G ⧸ Λ) :
    quotientRightTranslation (k := k) Λ (c * c') = quotientRightTranslation Λ c' ≫ quotientRightTranslation Λ c := by
  apply Rep.hom_ext; refine DFunLike.ext _ _ fun x => ?_
  show Finsupp.mapDomain (· * (c * c')⁻¹) x = Finsupp.mapDomain (· * c⁻¹) (Finsupp.mapDomain (· * c'⁻¹) x)
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext q
  show q * (c * c')⁻¹ = q * c'⁻¹ * c⁻¹
  rw [mul_inv_rev, mul_assoc]

@[simp] theorem quotientRightTranslationTwist_hom_apply (χ : G →* kˣ) (c : G ⧸ Λ) (x : G ⧸ Λ →₀ k) :
    (quotientRightTranslationTwist (k := k) Λ χ c).hom x = Finsupp.mapDomain (· * c⁻¹) x := rfl

theorem quotientRightTranslationTwist_hom_single (χ : G →* kˣ) (c q : G ⧸ Λ) (a : k) :
    (quotientRightTranslationTwist (k := k) Λ χ c).hom (Finsupp.single q a) = Finsupp.single (q * c⁻¹) a := by
  rw [quotientRightTranslationTwist_hom_apply, Finsupp.mapDomain_single]

end Rep
