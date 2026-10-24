/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IntersectionMultSingularPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.LocalIntersectionMultiplicity
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.LocalIntersectionMultiplicity
import Mathlib.Algebra.MvPolynomial.PDeriv

noncomputable section

open MvPolynomial Module

namespace IntersectionMultSingular

variable (k : Type*) [Field k]

/-- Evaluation ring homomorphism at the point `(a, b) ∈ k²`. -/
def evalAtPoint (a b : k) : MvPolynomial (Fin 2) k →+* k :=
  MvPolynomial.eval (fun i => if i = 0 then a else b)

/-- Predicate: the point `(a, b)` lies on the curve `f = 0`. -/
def PointOnCurve (f : MvPolynomial (Fin 2) k) (a b : k) : Prop :=
  evalAtPoint k a b f = 0

/-- A plane curve `f` is singular at `(a, b)` if both partial derivatives vanish at
the point and the point lies on the curve. -/
def IsSingularAt (f : MvPolynomial (Fin 2) k) (a b : k) : Prop :=
  PointOnCurve k f a b ∧
  evalAtPoint k a b (MvPolynomial.pderiv (0 : Fin 2) f) = 0 ∧
  evalAtPoint k a b (MvPolynomial.pderiv (1 : Fin 2) f) = 0

/-- Corollary 20: if one of the two plane curves `f, g` is singular at a common point
`(a, b)`, the local intersection multiplicity at that point is at least two. -/
end IntersectionMultSingular

end
