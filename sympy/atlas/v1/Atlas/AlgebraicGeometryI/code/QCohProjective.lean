/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.GradedPolynomial
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

/-- Degree-`d` homogeneous component of the homogeneous coordinate ring of `ℙ^n_k`. -/
def gradedComponent (k : Type*) [CommSemiring k] (n d : ℕ) :
    Submodule k (HomogCoordRing k n) :=
  homogeneousSubmodule (Fin (n + 1)) k d

/-- The irrelevant ideal `(X_0, …, X_n)` of the homogeneous coordinate ring of `ℙ^n_k`. -/
def irrelevantIdeal (k : Type*) [CommSemiring k] (n : ℕ) :
    Ideal (HomogCoordRing k n) :=
  Ideal.span (Set.range (fun i : Fin (n + 1) => MvPolynomial.X i))

/-- Abstract data of a graded module over the homogeneous coordinate ring of
`ℙ^n_k`: an integer-indexed family of `k`-vector spaces with a graded
multiplication action by homogeneous polynomials. -/
structure GradedModuleData (k : Type*) [Field k] (n : ℕ) where
  component : ℤ → Type*
  instACG : ∀ d : ℤ, AddCommGroup (component d)
  instMod : ∀ d : ℤ, Module k (component d)
  gsmul : ∀ (i : ℕ) (j : ℤ), gradedComponent k n i → component j → component (↑i + j)

attribute [instance] GradedModuleData.instACG GradedModuleData.instMod

/-- Degree shift `M ↦ M(d)` of a graded module, corresponding to tensoring
with the twist `𝒪(d)` on `ℙ^n_k`. -/
def GradedModuleData.twist {k : Type*} [Field k] {n : ℕ}
    (M : GradedModuleData k n) (d : ℤ) : GradedModuleData k n where
  component i := M.component (i + d)
  instACG i := M.instACG (i + d)
  instMod i := M.instMod (i + d)
  gsmul a j s m := cast (by congr 1; omega) (M.gsmul a (j + d) s m)
