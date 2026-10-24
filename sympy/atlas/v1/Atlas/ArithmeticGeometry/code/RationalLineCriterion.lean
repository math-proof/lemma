/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RationalLineCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.ClassGroupRatFunc
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.DegreePullback
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.DegreePullback

namespace ArithmeticGeometry

/-- An axiomatic structure for a smooth projective curve $C/k$: it bundles the function field, divisor group, degree-zero Picard group $\operatorname{Pic}^0(C)$, set of rational points, principal divisor map, class map, genus, and the basic compatibilities between them. -/
structure SmoothProjectiveCurve (k : Type*) [Field k] where
  FunField : Type*
  [fieldInst : Field FunField]
  [algebraInst : Algebra k FunField]
  DivGroup : Type*
  [divGroupInst : AddCommGroup DivGroup]
  Pic0 : Type*
  [pic0Inst : AddCommGroup Pic0]
  RatPoint : Type*
  pointToDivisor : RatPoint → DivGroup
  degreeMap : DivGroup →+ ℤ
  degree_point : ∀ P : RatPoint, degreeMap (pointToDivisor P) = 1
  principalDiv : FunField → DivGroup
  degree_principalDiv : ∀ f : FunField, degreeMap (principalDiv f) = 0
  classMap : DivGroup →+ Pic0
  principalDiv_in_kernel : ∀ f : FunField, f ≠ 0 → classMap (principalDiv f) = 0
  classMap_surj : ∀ x : Pic0, ∃ D : DivGroup, degreeMap D = 0 ∧ classMap D = x
  classMap_eq_zero_iff : ∀ D : DivGroup, degreeMap D = 0 →
    (classMap D = 0 ↔ ∃ f : FunField, f ≠ 0 ∧ principalDiv f = D)
  pointToDivisor_injective : Function.Injective pointToDivisor
  principalDiv_algebraMap : ∀ a : k, principalDiv (algebraMap k FunField a) = 0
  isAlgebraic_implies_mem_range_algebraMap :
    ∀ f : FunField, IsAlgebraic k f → f ∈ Set.range (algebraMap k FunField)
  genusVal : ℕ
  exists_two_ratPoints_of_algClosed : IsAlgClosed k → ∃ P Q : RatPoint, P ≠ Q
  principalDiv_mul : ∀ (f g : FunField), f ≠ 0 → g ≠ 0 →
    principalDiv (f * g) = principalDiv f + principalDiv g

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
