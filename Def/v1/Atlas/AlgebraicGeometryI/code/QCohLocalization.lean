/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohLocalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec14QCohProjective
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.Lec14QCohProjective
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.QCohLocalization

@[expose] public section

namespace QCohLocalization

open LocalizedModule

/-- Every quasi-coherent sheaf on `Spec R` lies in the essential image of the
tilde functor (the Thm 12.1 direction). -/
noncomputable def tildeSpec_globalSectionsModule (F : (Spec R).Modules) :
    ModuleCat.{u} R :=
  moduleSpecΓFunctor.obj F

end QCohLocalization
