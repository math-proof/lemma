/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicGeometryI.code.GradedPolynomial
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.GradedPolynomial
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.Algebra.DirectSum.Basic
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.QCohProjective

@[expose] public section

set_option maxHeartbeats 4000000

open MvPolynomial


noncomputable section

namespace QCohProjective

/-- Degree-`d` homogeneous component of the homogeneous coordinate ring of `ℙ^n_k`. -/
def gradedComponent (k : Type*) [CommSemiring k] (n d : ℕ) :
    Submodule k (HomogCoordRing k n) :=
  homogeneousSubmodule (Fin (n + 1)) k d

/-- The irrelevant ideal `(X_0, …, X_n)` of the homogeneous coordinate ring of `ℙ^n_k`. -/
def irrelevantIdeal (k : Type*) [CommSemiring k] (n : ℕ) :
    Ideal (HomogCoordRing k n) :=
  Ideal.span (Set.range (fun i : Fin (n + 1) => MvPolynomial.X i))

end QCohProjective
end
