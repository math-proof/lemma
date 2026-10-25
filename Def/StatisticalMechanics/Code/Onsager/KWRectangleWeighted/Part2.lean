/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleWeighted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.KWRectangleCritical.Part4
import Theorem.StatisticalMechanics.Code.Onsager.KWRectangleWeighted


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


noncomputable def ons_rectWeightedWalkExponent (M N : Nat)
    (weight : ons_RectDart M N -> Complex) : Complex :=
  ∑' n : Nat,
    (∑ v : Fin (n + 1) -> ons_RectDart M N,
      ∏ k : Fin (n + 1),
        ons_rectKWmatDartWeighted M N weight (v k) (v (k + 1))) /
      (n + 1)


noncomputable def ons_rectDartSignDefect (M N : Nat)
    (defect : ons_RectDart M N -> Prop) [DecidablePred defect]
    (q : Real) (d : ons_RectDart M N) : Complex :=
  if defect d then -(q : Complex) else (q : Complex)

end StatMech.Onsager
