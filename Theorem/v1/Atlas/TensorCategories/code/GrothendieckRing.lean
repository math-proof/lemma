/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Instance.v1.Atlas.TensorCategories.code.GrothendieckRing
set_option maxHeartbeats 800000

open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

namespace GrRingOf

variable {R : FusionRing ι}

/-- The coefficient of the zero element is zero. -/
@[simp] lemma coeff_zero (k : ι) : (0 : GrRingOf R).coeff k = 0 := rfl

/-- Coefficients distribute over addition. -/
@[simp] lemma coeff_add (a b : GrRingOf R) (k : ι) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl

/-- Coefficients distribute over negation. -/
@[simp] lemma coeff_neg (a : GrRingOf R) (k : ι) :
    (-a).coeff k = -a.coeff k := rfl

/-- Coefficients distribute over subtraction. -/
@[simp] lemma coeff_sub (a b : GrRingOf R) (k : ι) :
    (a - b).coeff k = a.coeff k - b.coeff k := rfl

end GrRingOf
end FusionRing
