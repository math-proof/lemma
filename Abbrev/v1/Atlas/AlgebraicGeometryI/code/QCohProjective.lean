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
set_option maxHeartbeats 4000000

open MvPolynomial


@[expose] public noncomputable section

namespace QCohProjective

/-- Homogeneous coordinate ring `k[X_0, …, X_n]` of `ℙ^n_k`. -/
abbrev HomogCoordRing (k : Type*) [CommSemiring k] (n : ℕ) := MvPolynomial (Fin (n + 1)) k

end QCohProjective
end
