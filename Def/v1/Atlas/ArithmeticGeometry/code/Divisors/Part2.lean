/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.DegreePullback
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.DegreePullback
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RationalLineCriterion
import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
import Abbrev.v1.Atlas.ArithmeticGeometry.code.Divisors
attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional


namespace CurveDivisor

variable {C : Type*}

noncomputable def coeff (D : CurveDivisor C) (P : C) : ℤ := D P

noncomputable def divisorSupport (D : CurveDivisor C) : Finset C := D.support

variable (C) in
noncomputable def degree : CurveDivisor C →+ ℤ :=
  Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ)

noncomputable def degreeWeighted (deg : C → ℕ) : CurveDivisor C →+ ℤ :=
  Finsupp.liftAddHom (fun p => (deg p : ℤ) • AddMonoidHom.id ℤ)

end CurveDivisor
