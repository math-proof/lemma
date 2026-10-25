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
import Def.v1.Atlas.AlgebraicGeometryI.code.QCohLocalization


namespace QCohLocalization

open LocalizedModule

/-- The unit of the `tilde ⊣ Γ` adjunction is an isomorphism, expressing
the identity `Γ(M̃) ≅ M`. -/
instance tildeSpec_unitIso : IsIso (tilde.adjunction (R := R)).unit :=
  inferInstance

/-- The sheaf `M̃` on `Spec R` is quasi-coherent for any `R`-module `M`. -/
instance tildeSpec_isQuasicoherent (M : ModuleCat.{u} R) :
    (tilde M).IsQuasicoherent :=
  inferInstance

end QCohLocalization
