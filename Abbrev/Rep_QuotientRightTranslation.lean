import Mathlib
import Abbrev.Compat_Mathlib430
import Abbrev.GroupCohomology_Selmer

set_option autoImplicit false

open CategoryTheory

namespace Rep

universe u

variable {k : Type u} [CommRing k] {G : Type u} [Group G] (Λ : Subgroup G) [Λ.Normal]

private theorem smul_quotient_eq_mul (g : G) (q : G ⧸ Λ) : g • q = (g : G ⧸ Λ) * q := by
  induction q using QuotientGroup.induction_on with
  | H a => rfl

noncomputable def quotientRightTranslation (c : G ⧸ Λ) :
    Rep.ofMulActionFinsupp k G (G ⧸ Λ) ⟶ Rep.ofMulActionFinsupp k G (G ⧸ Λ) :=
  Rep.ofHom ⟨Finsupp.lmapDomain k k (· * c⁻¹), fun g => by
    apply LinearMap.ext; intro x
    show Finsupp.lmapDomain k k (· * c⁻¹) (Representation.ofMulActionFinsupp k G (G ⧸ Λ) g x) =
      Representation.ofMulActionFinsupp k G (G ⧸ Λ) g (Finsupp.lmapDomain k k (· * c⁻¹) x)
    rw [Representation.ofMulActionFinsupp_def, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply,
      Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 1
    funext q
    show g • q * c⁻¹ = g • (q * c⁻¹)
    rw [smul_quotient_eq_mul, smul_quotient_eq_mul, mul_assoc]⟩

noncomputable def quotientRightTranslationTwist (χ : G →* kˣ) (c : G ⧸ Λ) :
    (Rep.ofMulActionFinsupp k G (G ⧸ Λ)).twist χ ⟶ (Rep.ofMulActionFinsupp k G (G ⧸ Λ)).twist χ :=
  Rep.ofHom ⟨Finsupp.lmapDomain k k (· * c⁻¹), fun g => by
    apply LinearMap.ext; intro x
    show Finsupp.lmapDomain k k (· * c⁻¹) (((Rep.ofMulActionFinsupp k G (G ⧸ Λ)).ρ.twist χ) g x) =
      ((Rep.ofMulActionFinsupp k G (G ⧸ Λ)).ρ.twist χ) g (Finsupp.lmapDomain k k (· * c⁻¹) x)
    rw [Representation.twist_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    congr 1
    exact Rep.hom_comm_apply (quotientRightTranslation (k := k) Λ c) g x⟩

end Rep
