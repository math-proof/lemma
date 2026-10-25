/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.BigOperators
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Basic
open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*}

variable [DecidableEq B] [Fintype B]

/-- The bilinear form on $\mathbb{R}^B$ associated to the Coxeter matrix $M$,
defined by $B(v, w) = \sum_{s,t} v_s\, B_{s,t}\, w_t$ where
$B_{s,t} = \mathtt{formVal}\,M\,s\,t$. This is the standard form making the
geometric representation orthogonal. -/
noncomputable def bilinForm (M : CoxeterMatrix B) (v w : B → ℝ) : ℝ :=
  ∑ s, ∑ t, v s * formVal M s t * w t

/-- The standard basis vector $e_s \in \mathbb{R}^B$ supported at $s$ with value
$1$. -/
noncomputable def e (s : B) : B → ℝ := Pi.single s 1

end CoxeterGroup
