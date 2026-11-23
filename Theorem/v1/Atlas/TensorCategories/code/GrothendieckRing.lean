/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
public import Theorem.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Ring.Defs
public import Instance.v1.Atlas.TensorCategories.code.GrothendieckRing
set_option maxHeartbeats 800000

open Finset

public section

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
