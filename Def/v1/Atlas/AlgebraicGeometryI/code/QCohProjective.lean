/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.GradedPolynomial
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GradedPolynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.Module
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Algebra.DirectSum.Basic
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.QCohProjective
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
