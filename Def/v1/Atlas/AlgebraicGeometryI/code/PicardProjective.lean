/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Instance.v1.Atlas.AlgebraicGeometryI.code.PicardProjective

@[expose] public section

noncomputable section

namespace PicardProjective

open MvPolynomial


/-- The class group of k[x_1,...,x_n] is isomorphic (as a group) to the trivial
group `Unit`. -/
def classGroup_mvPolynomial_mulEquiv_unit (k : Type*) [Field k] (n : ℕ) :
    ClassGroup (MvPolynomial (Fin n) k) ≃* (Unit : Type) := MulEquiv.ofUnique


end PicardProjective
end
