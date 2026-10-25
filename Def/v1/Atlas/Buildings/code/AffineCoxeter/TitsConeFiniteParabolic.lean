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
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

noncomputable def pairing (α x : B → ℝ) : ℝ :=
  ∑ s : B, α s * x s

def nonposRoots (Φpos : Set (B → ℝ)) (x : B → ℝ) : Set (B → ℝ) :=
  {α ∈ Φpos | pairing α x ≤ 0}

def nuFiniteAt (Φpos : Set (B → ℝ)) (x : B → ℝ) : Prop :=
  Set.Finite (nonposRoots Φpos x)

noncomputable def sigmaWord (M : CoxeterMatrix B) (ws : List B) (α : B → ℝ) : B → ℝ :=
  ws.foldl (fun v s => sigma M s v) α

noncomputable def dualSigmaWord (M : CoxeterMatrix B) (ws : List B) (x : B → ℝ) : B → ℝ :=
  ws.foldl (fun v s => dualSigma M s v) x

end TitsCone
