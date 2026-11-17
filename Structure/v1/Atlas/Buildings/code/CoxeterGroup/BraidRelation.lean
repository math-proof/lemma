/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Def.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3
public section

open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The braid relation hypothesis on the geometric representation: for every
pair $s, t$ with finite Coxeter order $m(s,t)$, the composition
$\sigma_s \sigma_t$ has order dividing $m(s,t)$ on the representation. -/
structure BraidRelationHyp (M : CoxeterMatrix B) where
  braid_power_eq_one : ∀ (s t : B), M.M s t ≠ 0 →
    ∀ (v : B → ℝ), (fun w => sigma M s (sigma M t w))^[M.M s t] v = v

end CoxeterGroup
