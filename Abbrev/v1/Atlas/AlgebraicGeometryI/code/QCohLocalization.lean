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

@[expose] public section


namespace QCohLocalization

open LocalizedModule

/-- The localized module `M_f := S^{-1} M` at the powers of `f`, encoding the
value `Γ(D(f), M̃)` of the tilde sheaf on a principal open. -/
abbrev ModuleTilde (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (f : R) : Type _ :=
  LocalizedModule (Submonoid.powers f) M

end QCohLocalization
