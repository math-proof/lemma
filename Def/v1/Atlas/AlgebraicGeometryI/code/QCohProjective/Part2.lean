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
public import Structure.v1.Atlas.AlgebraicGeometryI.code.QCohProjective

@[expose] public section

set_option maxHeartbeats 4000000

open MvPolynomial


noncomputable section

namespace QCohProjective

attribute [instance] GradedModuleData.instACG GradedModuleData.instMod

/-- Degree shift `M ↦ M(d)` of a graded module, corresponding to tensoring
with the twist `𝒪(d)` on `ℙ^n_k`. -/
def GradedModuleData.twist {k : Type*} [Field k] {n : ℕ}
    (M : GradedModuleData k n) (d : ℤ) : GradedModuleData k n where
  component i := M.component (i + d)
  instACG i := M.instACG (i + d)
  instMod i := M.instMod (i + d)
  gsmul a j s m := cast (by congr 1; omega) (M.gsmul a (j + d) s m)

end QCohProjective
end
