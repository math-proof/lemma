/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohLocalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Flat.Localization
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec14QCohProjective
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.Lec14QCohProjective


namespace QCohLocalization

open LocalizedModule

/-- The localized module `M_f := S^{-1} M` at the powers of `f`, encoding the
value `Γ(D(f), M̃)` of the tilde sheaf on a principal open. -/
abbrev ModuleTilde (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (f : R) : Type _ :=
  LocalizedModule (Submonoid.powers f) M

end QCohLocalization
