import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.CanonicalDivisors.Part2
open PicardGroup CanonicalDivisors


namespace PicardGroup

/--
[degPic_toPic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CanonicalDivisors.lean)
-/
@[path]
lemma degPic_toPic
  [AddCommGroup Div]
  {PrincDiv : AddSubgroup Div}
  {deg : Div →+ ℤ}
  {D : Div}
-- given
  (hdeg : PrincDiv ≤ deg.ker) :
-- imply
  degPic deg hdeg (toPic Div PrincDiv D) = deg D := by
-- proof
  simp [degPic, toPic, QuotientAddGroup.mk'_apply]

end PicardGroup

namespace PicardGroup

/--
[mem_Pic0_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CanonicalDivisors.lean)
-/
@[path]
lemma mem_Pic0_iff
  [AddCommGroup Div]
  {PrincDiv : AddSubgroup Div}
  {deg : Div →+ ℤ}
  {x : PicGrp Div PrincDiv}
-- given
  (hdeg : PrincDiv ≤ deg.ker) :
-- imply
  x ∈ Pic0 deg hdeg ↔ degPic deg hdeg x = 0 := by
-- proof
  simp [Pic0, AddMonoidHom.mem_ker]
end PicardGroup


namespace CanonicalDivisors

/--
[exists_maximal_divisor_for_nonzero_differential](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CanonicalDivisors.lean)
-/
@[path]
lemma exists_maximal_divisor_for_nonzero_differential
  [Field F]
  [AddCommGroup Div]
  [Zero Ω]
  {divF : F → Div}
  {divΩ : Ω → Div}
  {smulΩ : F → Ω → Ω}
  {ordP : Place → Div → ℤ}
  [SemilatticeSup Div]
  {ω : Ω}
-- given
  (omegaD : Ω → Div → Prop)
  (omegaD : Ω → Div → Prop)
  (_hω : ω ≠ 0)
  (hex : ∃ D, omegaD ω D)
  (hfin : Set.Finite {D | omegaD ω D})
  (hsup : ∀ D₁ D₂, omegaD ω D₁ → omegaD ω D₂ → omegaD ω (D₁ ⊔ D₂)) :
-- imply
  ∃ D, omegaD ω D ∧ ∀ D' : Div, omegaD ω D' → D' ≤ D := by
-- proof
  obtain ⟨D₀, hD₀⟩ := hex
  obtain ⟨m, hm⟩ := hfin.exists_maximal ⟨D₀, hD₀⟩
  refine ⟨m, hm.prop, fun D' hD' => ?_⟩
  exact le_trans le_sup_right (hm.le_of_ge (hsup m D' hm.prop hD') le_sup_left)

end CanonicalDivisors

namespace CanonicalDivisors

/--
[div_smul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CanonicalDivisors.lean)
-/
@[path]
lemma div_smul_eq
  [Field F]
  [AddCommGroup Div]
  [Zero Ω]
  {divF : F → Div}
  {divΩ : Ω → Div}
  {smulΩ : F → Ω → Ω}
  {ordP : Place → Div → ℤ}
  [PartialOrder Div]
  [CovariantClass Div Div (· + ·) (· ≤ ·)]
  {f : F}
  {ω : Ω}
-- given
  (omegaD : Ω → Div → Prop)
  (hf : f ≠ 0)
  (_hω : ω ≠ 0)
  (hdivΩ_max : ∀ (ω' : Ω), ω' ≠ 0 → IsDivOmegaMaximal divΩ omegaD ω')
  (omegaD_smul : ∀ (g : F), g ≠ 0 → ∀ (ω' : Ω) (D : Div), omegaD ω' D → omegaD (smulΩ g ω') (divF g + D))
  (smul_ne_zero : ∀ (g : F) (ω' : Ω), g ≠ 0 → ω' ≠ 0 → smulΩ g ω' ≠ 0)
  (divF_inv : ∀ (g : F), g ≠ 0 → divF g⁻¹ = -divF g)
  (smul_inv_cancel : ∀ (g : F) (ω' : Ω), g ≠ 0 → smulΩ g⁻¹ (smulΩ g ω') = ω') :
-- imply
  divΩ (smulΩ f ω) = divF f + divΩ ω := by
-- proof
  have hfω_ne : smulΩ f ω ≠ 0 := smul_ne_zero f ω hf _hω
  have hmax_ω := hdivΩ_max ω _hω
  have hmax_fω := hdivΩ_max (smulΩ f ω) hfω_ne
  apply le_antisymm
  ·
    have h1 := hmax_fω.mem
    have h2 := omegaD_smul f⁻¹ (inv_ne_zero hf) (smulΩ f ω) (divΩ (smulΩ f ω)) h1
    rw [smul_inv_cancel f ω hf] at h2
    have h3 := hmax_ω.le_divΩ _ h2
    rw [divF_inv f hf] at h3
    have h4 : (divF f) + (-divF f + divΩ (smulΩ f ω)) ≤ (divF f) + divΩ ω :=
      CovariantClass.elim (divF f) h3
    rwa [← add_assoc, add_neg_cancel, zero_add] at h4
  ·
    exact hmax_fω.le_divΩ _ (omegaD_smul f hf ω (divΩ ω) hmax_ω.mem)

end CanonicalDivisors

namespace CanonicalDivisors

/--
[canonical_linearlyEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CanonicalDivisors.lean)
-/
@[path]
lemma canonical_linearlyEquivalent
  [Field F]
  [AddCommGroup Div]
  [Zero Ω]
  {divF : F → Div}
  {divΩ : Ω → Div}
  {smulΩ : F → Ω → Ω}
  {ordP : Place → Div → ℤ}
  {D₁ D₂ : Div}
-- given
  (omegaD : Ω → Div → Prop)
  (omega_one_dim : ∀ ω₁ ω₂ : Ω, ω₁ ≠ 0 → ω₂ ≠ 0 → ∃ f : F, f ≠ 0 ∧ ω₂ = smulΩ f ω₁)
  (div_smul_eq : ∀ (f : F) (ω : Ω), f ≠ 0 → ω ≠ 0 → divΩ (smulΩ f ω) = divF f + divΩ ω)
  (h₁ : IsCanonical divΩ D₁)
  (h₂ : IsCanonical divΩ D₂) :
-- imply
  LinearlyEquivalent divF D₁ D₂ := by
-- proof
  obtain ⟨ω₁, hω₁_ne, rfl⟩ := h₁
  obtain ⟨ω₂, hω₂_ne, rfl⟩ := h₂
  obtain ⟨f, hf_ne, hf_eq⟩ := omega_one_dim ω₁ ω₂ hω₁_ne hω₂_ne
  exact ⟨f, hf_ne, by rw [hf_eq, div_smul_eq f ω₁ hf_ne hω₁_ne, add_comm]⟩

end CanonicalDivisors

namespace CanonicalDivisors

/--
[isCanonical_of_linearlyEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CanonicalDivisors.lean)
-/
@[path]
lemma isCanonical_of_linearlyEquivalent
  [Field F]
  [AddCommGroup Div]
  [Zero Ω]
  {divF : F → Div}
  {divΩ : Ω → Div}
  {smulΩ : F → Ω → Ω}
  {ordP : Place → Div → ℤ}
  {D₁ D₂ : Div}
-- given
  (omegaD : Ω → Div → Prop)
  (div_smul_eq : ∀ (f : F) (ω : Ω), f ≠ 0 → ω ≠ 0 → divΩ (smulΩ f ω) = divF f + divΩ ω)
  (smul_ne_zero : ∀ (f : F) (ω : Ω), f ≠ 0 → ω ≠ 0 → smulΩ f ω ≠ 0)
  (h₁ : IsCanonical divΩ D₁)
  (h₂ : LinearlyEquivalent divF D₁ D₂) :
-- imply
  IsCanonical divΩ D₂ := by
-- proof
  obtain ⟨ω₁, hω₁_ne, rfl⟩ := h₁
  obtain ⟨f, hf_ne, hf_eq⟩ := h₂
  exact ⟨smulΩ f ω₁, smul_ne_zero f ω₁ hf_ne hω₁_ne, by
    rw [hf_eq, div_smul_eq f ω₁ hf_ne hω₁_ne, add_comm]⟩

end CanonicalDivisors

namespace CanonicalDivisors

/--
[canonical_divisors_form_single_class](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CanonicalDivisors.lean)
-/
@[path]
lemma canonical_divisors_form_single_class
  [Field F]
  [AddCommGroup Div]
  [Zero Ω]
  {divF : F → Div}
  {divΩ : Ω → Div}
  {smulΩ : F → Ω → Ω}
  {ordP : Place → Div → ℤ}
  {D₁ D₂ : Div}
-- given
  (omegaD : Ω → Div → Prop)
  (omega_one_dim : ∀ ω₁ ω₂ : Ω, ω₁ ≠ 0 → ω₂ ≠ 0 → ∃ f : F, f ≠ 0 ∧ ω₂ = smulΩ f ω₁)
  (div_smul_eq : ∀ (f : F) (ω : Ω), f ≠ 0 → ω ≠ 0 → divΩ (smulΩ f ω) = divF f + divΩ ω)
  (smul_ne_zero : ∀ (f : F) (ω : Ω), f ≠ 0 → ω ≠ 0 → smulΩ f ω ≠ 0)
  (h₁ : IsCanonical divΩ D₁) :
-- imply
  IsCanonical divΩ D₂ ↔ LinearlyEquivalent divF D₁ D₂ := by
-- proof
  constructor
  · intro h₂
    exact canonical_linearlyEquivalent divF divΩ smulΩ omega_one_dim div_smul_eq h₁ h₂
  · intro h₂
    exact isCanonical_of_linearlyEquivalent divF divΩ smulΩ div_smul_eq smul_ne_zero h₁ h₂

end CanonicalDivisors

namespace CanonicalDivisors

/--
[cor_22_19_weil_diff_same_div](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CanonicalDivisors.lean)
-/
@[path]
lemma cor_22_19_weil_diff_same_div
  [Field F]
  [AddCommGroup Div]
  [Zero Ω]
  {divF : F → Div}
  {divΩ : Ω → Div}
  {smulΩ : F → Ω → Ω}
  {ordP : Place → Div → ℤ}
  [Field k]
  [Algebra k F]
  {ω₁ ω₂ : Ω}
-- given
  (omegaD : Ω → Div → Prop)
  (omega_one_dim : ∀ ω₁ ω₂ : Ω, ω₁ ≠ 0 → ω₂ ≠ 0 → ∃ f : F, f ≠ 0 ∧ ω₂ = smulΩ f ω₁)
  (div_smul_eq : ∀ (f : F) (ω : Ω), f ≠ 0 → ω ≠ 0 → divΩ (smulΩ f ω) = divF f + divΩ ω)
  (divF_zero_iff_const : ∀ (f : F), f ≠ 0 → (divF f = 0 ↔ ∃ c : k, c ≠ 0 ∧ algebraMap k F c = f))
  (divF_const_zero : ∀ (c : k), c ≠ 0 → divF (algebraMap k F c) = 0)
  (hω₁ : ω₁ ≠ 0)
  (hω₂ : ω₂ ≠ 0) :
-- imply
  divΩ ω₁ = divΩ ω₂ ↔ ∃ c : k, c ≠ 0 ∧ ω₂ = smulΩ (algebraMap k F c) ω₁ := by
-- proof
  constructor
  ·
    intro hdiv_eq
    obtain ⟨f, hf_ne, hf_eq⟩ := omega_one_dim ω₁ ω₂ hω₁ hω₂
    have h_divf_zero : divF f = 0 := by
      have h1 : divΩ ω₁ = divF f + divΩ ω₁ := by
        calc divΩ ω₁ = divΩ ω₂ := hdiv_eq
          _ = divΩ (smulΩ f ω₁) := by rw [hf_eq]
          _ = divF f + divΩ ω₁ := div_smul_eq f ω₁ hf_ne hω₁
      exact add_eq_right.mp h1.symm
    obtain ⟨c, hc_ne, hc_eq⟩ := (divF_zero_iff_const f hf_ne).mp h_divf_zero
    exact ⟨c, hc_ne, by rw [hf_eq, hc_eq]⟩
  ·
    rintro ⟨c, hc_ne, hc_eq⟩
    have hc_ne_F : algebraMap k F c ≠ 0 :=
      fun h => hc_ne ((algebraMap k F).injective (h.trans (map_zero _).symm))
    rw [hc_eq, div_smul_eq (algebraMap k F c) ω₁ hc_ne_F hω₁,
      divF_const_zero c hc_ne, zero_add]

end CanonicalDivisors


-- created on 2026-10-23
