/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleWeighted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.KWRectangleCritical.Part4


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


noncomputable def ons_rectKWmatDartWeighted (M N : Nat)
    (weight : ons_RectDart M N -> Complex) :
    Matrix (ons_RectDart M N) (ons_RectDart M N) Complex :=
  (ons_rectDartMask M N * ons_arrivalTurnMatrixOf (ons_RectVertex M N) *
      (ons_rectTailDartEquiv M N).permMatrix Complex * ons_rectDartMask M N) *
    Matrix.diagonal weight


end StatMech.Onsager
