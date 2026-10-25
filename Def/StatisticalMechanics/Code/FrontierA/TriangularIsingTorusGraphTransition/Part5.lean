/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorContinuation
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGraphTransition.Part5


namespace StatMech.FrontierA

open SimpleGraph StatMech.Onsager

noncomputable def triangularTorusGraphPhase
    (L : Nat) [Fact (2 < L)] (rho u v : Complex)
    (d e : (triangularTorusGraph L).Dart) : Complex :=
  let d' := (triangularTorusDartEquiv L).symm d
  let e' := (triangularTorusDartEquiv L).symm e
  triangularTorusDirectionPhase u v d'.2 *
    triangularKacWardTurnMatrix rho d'.2 e'.2


end StatMech.FrontierA
