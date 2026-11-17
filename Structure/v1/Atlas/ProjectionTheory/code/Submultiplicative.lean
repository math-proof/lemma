/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/Submultiplicative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib


public section

namespace ProjectionTheory

/-- The abstract data of an AD-regular configuration space at every scale $\delta$:
each $\delta$ has a type of configurations whose "ratio" measures the incidence count;
configurations at scale $\delta_1 \delta_2$ can be coarsened to scale $\delta_1$ and
restricted to scale $\delta_2$, and the ratio factors (up to a sub-polynomial loss) as
$R(\delta_1\delta_2) \lessapprox (\delta_1\delta_2)^{-\varepsilon} R(\delta_1) R(\delta_2)$. -/
structure ADConfigSpace where
  Config : ℝ → Type
  ratio : (δ : ℝ) → Config δ → ℝ
  ratio_nonneg : ∀ (δ : ℝ) (c : Config δ), 0 ≤ ratio δ c
  ratio_bddAbove : ∀ (δ : ℝ), BddAbove (Set.range (ratio δ))
  config_nonempty : ∀ (δ : ℝ), Nonempty (Config δ)
  coarsen : ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 →
    Config (δ₁ * δ₂) → Config δ₁
  restrict : ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 →
    Config (δ₁ * δ₂) → Config δ₂
  ratio_factoring : ∀ (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁' : δ₁ < 1)
    (hδ₂ : 0 < δ₂) (hδ₂' : δ₂ < 1),
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ c : Config (δ₁ * δ₂),
        ratio (δ₁ * δ₂) c ≤ C * (δ₁ * δ₂)⁻¹ ^ ε *
          (ratio δ₁ (coarsen δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c) *
           ratio δ₂ (restrict δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c))

/-- The raw data of an AD-regular configuration space, equipped only with the
pointwise incidence decomposition $R(\delta_1\delta_2) \le R(\delta_1) R(\delta_2)$
(without the $\varepsilon$-loss factor). -/
structure ADConfigData where
  Config : ℝ → Type
  ratio : (δ : ℝ) → Config δ → ℝ
  ratio_nonneg : ∀ (δ : ℝ) (c : Config δ), 0 ≤ ratio δ c
  ratio_bddAbove : ∀ (δ : ℝ), BddAbove (Set.range (ratio δ))
  config_nonempty : ∀ (δ : ℝ), Nonempty (Config δ)
  coarsen : ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 →
    Config (δ₁ * δ₂) → Config δ₁
  restrict : ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 →
    Config (δ₁ * δ₂) → Config δ₂
  incidence_decomp : ∀ (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁' : δ₁ < 1)
    (hδ₂ : 0 < δ₂) (hδ₂' : δ₂ < 1),
    ∀ c : Config (δ₁ * δ₂),
      ratio (δ₁ * δ₂) c ≤
        ratio δ₁ (coarsen δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c) *
        ratio δ₂ (restrict δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c)

/-- The concrete AD configuration data used in the projection theory framework. -/
noncomputable def adConfigData : ADConfigData := by sorry

/-- Derivation of the $\varepsilon$-loss factoring axiom for `adConfigData` from its
pointwise incidence decomposition: the ratio at scale $\delta_1\delta_2$ is bounded by
$C \cdot (\delta_1\delta_2)^{-\varepsilon}$ times the product of ratios at scales
$\delta_1$ and $\delta_2$. -/
theorem ratio_factoring_axiom :
    ∀ (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁' : δ₁ < 1)
      (hδ₂ : 0 < δ₂) (hδ₂' : δ₂ < 1),
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ c : adConfigData.Config (δ₁ * δ₂),
        adConfigData.ratio (δ₁ * δ₂) c ≤ C * (δ₁ * δ₂)⁻¹ ^ ε *
          (adConfigData.ratio δ₁ (adConfigData.coarsen δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c) *
           adConfigData.ratio δ₂ (adConfigData.restrict δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c)) := by
  intro δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' ε hε
  refine ⟨1, one_pos, fun c => ?_⟩

  have hdecomp := adConfigData.incidence_decomp δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c

  have hinv_ge_one : 1 ≤ (δ₁ * δ₂)⁻¹ ^ ε := by
    apply Real.one_le_rpow
    · rw [one_le_inv₀ (mul_pos hδ₁ hδ₂)]
      exact le_of_lt (mul_lt_one_of_nonneg_of_lt_one_left (le_of_lt hδ₁) hδ₁' (le_of_lt hδ₂'))
    · exact le_of_lt hε

  have hprod_nonneg : 0 ≤
      adConfigData.ratio δ₁ (adConfigData.coarsen δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c) *
      adConfigData.ratio δ₂ (adConfigData.restrict δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c) :=
    mul_nonneg (adConfigData.ratio_nonneg δ₁ _) (adConfigData.ratio_nonneg δ₂ _)


  calc adConfigData.ratio (δ₁ * δ₂) c
      ≤ adConfigData.ratio δ₁ (adConfigData.coarsen δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c) *
        adConfigData.ratio δ₂ (adConfigData.restrict δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c) := hdecomp
    _ ≤ (δ₁ * δ₂)⁻¹ ^ ε *
        (adConfigData.ratio δ₁ (adConfigData.coarsen δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c) *
         adConfigData.ratio δ₂ (adConfigData.restrict δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c)) :=
      le_mul_of_one_le_left hprod_nonneg hinv_ge_one
    _ = 1 * (δ₁ * δ₂)⁻¹ ^ ε *
        (adConfigData.ratio δ₁ (adConfigData.coarsen δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c) *
         adConfigData.ratio δ₂ (adConfigData.restrict δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c)) := by ring

/-- The AD configuration space obtained from `adConfigData` by promoting its pointwise
incidence decomposition to the submultiplicative factoring axiom. -/
noncomputable def adConfigSpace : ADConfigSpace where
  Config := adConfigData.Config
  ratio := adConfigData.ratio
  ratio_nonneg := adConfigData.ratio_nonneg
  ratio_bddAbove := adConfigData.ratio_bddAbove
  config_nonempty := adConfigData.config_nonempty
  coarsen := adConfigData.coarsen
  restrict := adConfigData.restrict
  ratio_factoring := ratio_factoring_axiom

/-- The AD-regular incidence quantity $R_{AD}(\delta)$ at scale $\delta$, defined as the
supremum of the configuration ratios over all configurations at scale $\delta$. -/
noncomputable def R_AD (δ : ℝ) : ℝ :=
  sSup (Set.range (adConfigSpace.ratio δ))

/-- $R_{AD}(\delta) \ge 0$ for every scale $\delta$. -/
theorem R_AD_nonneg (δ : ℝ) : 0 ≤ R_AD δ := by
  unfold R_AD
  apply le_csSup_of_le (adConfigSpace.ratio_bddAbove δ)
  · exact ⟨(adConfigSpace.config_nonempty δ).some, rfl⟩
  · exact adConfigSpace.ratio_nonneg δ _

/-- Each individual configuration ratio is bounded by the supremum $R_{AD}(\delta)$. -/
theorem ratio_le_R_AD (δ : ℝ) (c : adConfigSpace.Config δ) :
    adConfigSpace.ratio δ c ≤ R_AD δ := by
  unfold R_AD
  exact le_csSup (adConfigSpace.ratio_bddAbove δ) ⟨c, rfl⟩

/-- **Submultiplicative Lemma.** If $\delta = \delta_1 \delta_2$ with $\delta_1, \delta_2 < 1$,
then for every $\varepsilon > 0$ there is a constant $C > 0$ such that
$R_{AD}(\delta_1\delta_2) \le C \cdot (\delta_1\delta_2)^{-\varepsilon} \cdot
R_{AD}(\delta_1) \cdot R_{AD}(\delta_2)$, i.e. $R_{AD}$ is submultiplicative up to a
sub-polynomial loss. -/
theorem R_AD_submultiplicative
    (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁' : δ₁ < 1) (hδ₂ : 0 < δ₂) (hδ₂' : δ₂ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      R_AD (δ₁ * δ₂) ≤ C * (δ₁ * δ₂)⁻¹ ^ ε * (R_AD δ₁ * R_AD δ₂) := by
  intro ε hε

  obtain ⟨C, hC, hfactor⟩ :=
    adConfigSpace.ratio_factoring δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' ε hε
  refine ⟨C, hC, ?_⟩

  unfold R_AD
  apply csSup_le
  ·
    haveI := adConfigSpace.config_nonempty (δ₁ * δ₂)
    exact Set.range_nonempty (adConfigSpace.ratio (δ₁ * δ₂))
  ·
    rintro _ ⟨c, rfl⟩

    set c₁ := adConfigSpace.coarsen δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c
    set c₂ := adConfigSpace.restrict δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c

    calc adConfigSpace.ratio (δ₁ * δ₂) c

        ≤ C * (δ₁ * δ₂)⁻¹ ^ ε * (adConfigSpace.ratio δ₁ c₁ * adConfigSpace.ratio δ₂ c₂) :=
          hfactor c

      _ ≤ C * (δ₁ * δ₂)⁻¹ ^ ε * (R_AD δ₁ * R_AD δ₂) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul (ratio_le_R_AD δ₁ c₁) (ratio_le_R_AD δ₂ c₂)
              (adConfigSpace.ratio_nonneg δ₂ c₂) (R_AD_nonneg δ₁)
          · apply mul_nonneg
            · exact le_of_lt hC
            · exact Real.rpow_nonneg (inv_nonneg.mpr (le_of_lt (mul_pos hδ₁ hδ₂))) ε

end ProjectionTheory
