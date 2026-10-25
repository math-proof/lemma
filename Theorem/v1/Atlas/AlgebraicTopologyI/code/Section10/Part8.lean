/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section10.Part6
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace BrouwerFixedPoint

open Metric Set Inner

variable {X : Type u} [TopologicalSpace X]

/-- Any endomorphism `f : ℤ ⟶ ℤ` in `AddCommGrp` is multiplication by `f 1`. -/
lemma addCommGrpCat_endZ_apply
    (f : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) (x : ℤ) :
    f x = f 1 * x := by
  change (ConcreteCategory.hom f) x = (ConcreteCategory.hom f) 1 * x
  have h := (ConcreteCategory.hom f).map_zsmul 1 x
  simp only [smul_eq_mul, mul_one] at h
  rw [h, mul_comm]

end BrouwerFixedPoint
