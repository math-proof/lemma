/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SubmultiplicativeProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.ProjectionTheory.code.Submultiplicative
import Lemma.Real.Atlas.v1.ProjectionTheory.code.Submultiplicative


namespace ProjectionTheory

/-- The abstract data of a *projective* AD-regular configuration space at every scale
$\delta$. Each projective configuration embeds into the AD configuration space with matching
ratios, and admits a constant-loss decomposition: there exists $C > 0$ such that for every
factorization $\delta = \delta_1 \delta_2$ and every configuration $c$ at scale $\delta$,
there are configurations $c_1, c_2$ at scales $\delta_1, \delta_2$ with ratio bound
$\mathrm{ratio}(c) \le C \cdot \mathrm{ratio}(c_1) \cdot \mathrm{ratio}(c_2)$. -/
structure ProjectiveConfigSpace where
  Config : ℝ → Type
  ratio : (δ : ℝ) → Config δ → ℝ
  ratio_nonneg : ∀ (δ : ℝ) (c : Config δ), 0 ≤ ratio δ c
  ratio_bddAbove : ∀ (δ : ℝ), BddAbove (Set.range (ratio δ))
  config_nonempty : ∀ (δ : ℝ), Nonempty (Config δ)
  embed : (δ : ℝ) → Config δ → adConfigSpace.Config δ
  embed_ratio : ∀ (δ : ℝ) (c : Config δ), ratio δ c = adConfigSpace.ratio δ (embed δ c)
  decompose : ∃ C : ℝ, 0 < C ∧ ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 →
    ∀ c : Config (δ₁ * δ₂), ∃ c₁ : Config δ₁, ∃ c₂ : Config δ₂,
      ratio (δ₁ * δ₂) c ≤ C * (ratio δ₁ c₁ * ratio δ₂ c₂)

/-- The raw data underlying a projective AD configuration space: configurations with
explicit coarsen/restrict maps, and the pointwise incidence decomposition bound with
a universal constant $C$. -/
structure ProjectiveConfigData where
  Config : ℝ → Type
  ratio : (δ : ℝ) → Config δ → ℝ
  ratio_nonneg : ∀ (δ : ℝ) (c : Config δ), 0 ≤ ratio δ c
  ratio_bddAbove : ∀ (δ : ℝ), BddAbove (Set.range (ratio δ))
  config_nonempty : ∀ (δ : ℝ), Nonempty (Config δ)
  embed : (δ : ℝ) → Config δ → adConfigSpace.Config δ
  embed_ratio : ∀ (δ : ℝ) (c : Config δ), ratio δ c = adConfigSpace.ratio δ (embed δ c)
  coarsen : ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 →
    Config (δ₁ * δ₂) → Config δ₁
  restrict : ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 →
    Config (δ₁ * δ₂) → Config δ₂
  incidence_decomp : ∃ C : ℝ, 0 < C ∧ ∀ (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁' : δ₁ < 1)
    (hδ₂ : 0 < δ₂) (hδ₂' : δ₂ < 1),
    ∀ c : Config (δ₁ * δ₂),
      ratio (δ₁ * δ₂) c ≤ C *
        (ratio δ₁ (coarsen δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c) *
         ratio δ₂ (restrict δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c))

end ProjectionTheory
