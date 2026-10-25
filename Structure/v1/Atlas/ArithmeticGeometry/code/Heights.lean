/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.ArithmeticGeometry.code.GaloisPlaceHelper
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisPlaceHelper
import Def.v1.Atlas.ArithmeticGeometry.code.Heights.Part2


noncomputable section

open Height MvPolynomial

namespace AbsoluteHeight

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Empty.Finite ι]

structure TwoIsogenyData (W : WeierstrassCurve ℚ) [W.IsElliptic] where
  E'Points : Type
  instAddCommGroup : AddCommGroup E'Points
  phi : W.toAffine.Point →+ E'Points
  phi_hat : E'Points →+ W.toAffine.Point
  comp_eq : phi_hat.comp phi = zsmulAddGroupHom (2 : ℤ)
  descentTarget : Type
  instDescentTargetGroup : AddCommGroup descentTarget
  descentMap : E'Points →+ descentTarget
  descentMap_range_finite : Empty.Finite descentMap.range
  descentMap_ker_eq : descentMap.ker = phi.range
  descentTarget' : Type
  instDescentTarget'Group : AddCommGroup descentTarget'
  descentMap' : W.toAffine.Point →+ descentTarget'
  descentMap'_range_finite : Empty.Finite descentMap'.range
  descentMap'_ker_eq : descentMap'.ker = phi_hat.range
  phi_hat_ker_le_phi_range : phi_hat.ker ≤ phi.range

end AbsoluteHeight
end
