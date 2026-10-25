/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part7
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PicardProjective
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DivisorsPicard
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PrincipalDivisorDegree
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutTheorem
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.LinearEquivDivisors
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PowerSeriesUFD
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PicardGroup
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SmoothCurveDivisors
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.DivisorsPicard.Part3
import Def.v1.Atlas.AlgebraicGeometryI.code.PrincipalDivisorDegree.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutTheorem
import Def.v1.Atlas.AlgebraicGeometryI.code.LinearEquivDivisors.Part3
import Instance.v1.Atlas.AlgebraicGeometryI.code.PowerSeriesUFD
import Instance.v1.Atlas.AlgebraicGeometryI.code.PicardGroup
import Def.v1.Atlas.AlgebraicGeometryI.code.SmoothCurveDivisors.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec15PicardDivisorClass.Part2
set_option maxHeartbeats 1600000


noncomputable section

namespace Lec15PicardDivisorClass

open Module Polynomial LinearEquivDivisors


/-- Degree of a Weil divisor; abbreviation for `WeilDivisor.degree`. -/
abbrev divisorDegree {Y : Type*} (D : DivisorsPicard.WeilDivisorGroup Y) : ℤ :=
  WeilDivisor.degree D


end Lec15PicardDivisorClass
end
