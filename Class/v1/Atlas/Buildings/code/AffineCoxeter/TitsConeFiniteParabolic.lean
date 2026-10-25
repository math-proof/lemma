/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeFiniteParabolic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity.Part3
import Mathlib.Order.Filter.Basic
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

class RootSystemData (M : CoxeterMatrix B) where
  Φpos : Set (B → ℝ)
  roots_in_subspan_finite : ∀ (I : Finset B), I ≠ Finset.univ →
    Set.Finite {α ∈ Φpos | ∀ s : B, s ∉ I → α s = 0}
  pos_pairing_outside_span :
    ∀ (I : Finset B) (x : B → ℝ),
      x ∈ titsFaceDual M I →
      ∀ α ∈ Φpos, (∃ s : B, s ∉ I ∧ α s ≠ 0) → pairing α x > 0
  pairing_word_comm :
    ∀ (ws : List B) (α x : B → ℝ),
      pairing α (dualSigmaWord M ws x) = pairing (sigmaWord M ws.reverse α) x
  sigmaWord_injective :
    ∀ (ws : List B), Function.Injective (sigmaWord M ws)
  inversions_finite : ∀ (ws : List B),
    Set.Finite {α ∈ Φpos | ¬ (sigmaWord M ws α ∈ Φpos)}
  simple_inversion : ∀ s : B,
    {α ∈ Φpos | ¬ (sigmaWord M [s] α ∈ Φpos)} = {CoxeterGroup.e s}
  nonposRoots_finite_on_hyperplane :
    ∀ (v₀ : B → ℝ),
    (∀ s, v₀ s > 0) →
    (∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0) →
    ∀ (x : B → ℝ), (∑ s, v₀ s * x s = 1) →
    Set.Finite (nonposRoots Φpos x)

end TitsCone
