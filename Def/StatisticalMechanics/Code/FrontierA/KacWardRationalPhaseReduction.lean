/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalPhaseReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonPerturbation.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleHomotopy.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalPhaseReduction


namespace StatMech.FrontierA

open scoped BigOperators

open Set

noncomputable def KWPolygonPerturbationCertificate.pathPolygon
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    (h : KWPolygonPerturbationCertificate polygon)
    (target : Fin n → ℂ) (htarget : dist target polygon.vertex < h.radius)
    (t : ℝ) : KWFiniteSimplePolygon n :=
  if ht : t ∈ Icc (0 : ℝ) 1 then
    (h.rawSimple (AffineMap.lineMap polygon.vertex target t)
      (dist_vertexLine_lt_certificate h htarget ht)).toFiniteSimplePolygon
  else polygon

end StatMech.FrontierA
