module
public import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
public import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity.Part3
public import Mathlib.Order.Filter.Basic
public import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic
set_option linter.unusedSectionVars false
open Finset BigOperators CoxeterGroup TitsCone


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeFiniteParabolic.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

noncomputable def standardΦpos (M : CoxeterMatrix B) : Set (B → ℝ) :=
  {α | (∃ (ws : List B) (s : B), α = sigmaWord M ws (CoxeterGroup.e s)) ∧ (∀ t, 0 ≤ α t)}

end TitsCone
