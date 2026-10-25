/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RationalLineCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.v1.Atlas.ArithmeticGeometry.code.ClassGroupRatFunc
import Def.v1.Atlas.ArithmeticGeometry.code.DegreePullback
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.DegreePullback
import Structure.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion


namespace ArithmeticGeometry

attribute [instance] SmoothProjectiveCurve.fieldInst
  SmoothProjectiveCurve.algebraInst
  SmoothProjectiveCurve.divGroupInst
  SmoothProjectiveCurve.pic0Inst

variable {k : Type*} [Field k]

/-- If there is a function $f \in k(C)$ with divisor $(P) - (Q)$ for distinct rational points $P, Q$, then any injective $k$-algebra map $\varphi: k(t) \to k(C)$ is automatically surjective. -/
def SmoothProjectiveCurve.IsIsomorphicToP1 (C : SmoothProjectiveCurve k) : Prop :=
  Nonempty (C.FunField ≃ₐ[k] RatFunc k)

/-- The Picard group $\operatorname{Pic}^0(C)$ is trivial iff every degree-zero divisor class is the identity. -/
def SmoothProjectiveCurve.Pic0IsTrivial (C : SmoothProjectiveCurve k) : Prop :=
  ∀ x : C.Pic0, x = 0

end ArithmeticGeometry
