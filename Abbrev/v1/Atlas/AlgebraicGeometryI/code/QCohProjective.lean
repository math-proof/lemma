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
set_option maxHeartbeats 4000000

open MvPolynomial


noncomputable section

namespace QCohProjective

/-- Homogeneous coordinate ring `k[X_0, …, X_n]` of `ℙ^n_k`. -/
abbrev HomogCoordRing (k : Type*) [CommSemiring k] (n : ℕ) := MvPolynomial (Fin (n + 1)) k

end QCohProjective
end
