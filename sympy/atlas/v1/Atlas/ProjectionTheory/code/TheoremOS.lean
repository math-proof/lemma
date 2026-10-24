/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/TheoremOS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ProjectionTheory.code.Submultiplicative
import Lemma.Real.Atlas.v1.ProjectionTheory.code.Submultiplicative

namespace ProjectionTheory

/-- Abstract data bundling the parameter space used to define
`R_{AD}(s, t, δ)` in the AD-regular case. For each triple `(s, t, δ)` it
provides:

* a type `Config s t δ` of admissible AD-regular configurations,
* a non-negative, bounded ratio functional `ratio s t δ : Config s t δ → ℝ`,
* an embedding into the un-parameterised `adConfigSpace.Config δ`
  preserving the ratio.

`R_AD_st s t δ` is then defined as the supremum of `ratio s t δ` over all
configurations. -/
structure ADConfigDataST where
  Config : ℝ → ℝ → ℝ → Type
  ratio : (s t δ : ℝ) → Config s t δ → ℝ
  ratio_nonneg : ∀ (s t δ : ℝ) (c : Config s t δ), 0 ≤ ratio s t δ c
  ratio_bddAbove : ∀ (s t δ : ℝ), BddAbove (Set.range (ratio s t δ))
  config_nonempty : ∀ (s t δ : ℝ), Nonempty (Config s t δ)
  embed : (s t δ : ℝ) → Config s t δ → adConfigSpace.Config δ
  embed_ratio : ∀ (s t δ : ℝ) (c : Config s t δ),
    adConfigSpace.ratio δ (embed s t δ c) = ratio s t δ c

/-- A chosen instance of `ADConfigDataST`: the concrete `(s, t)`-parameterised
AD-regular configuration data used throughout this section. -/
end ProjectionTheory
