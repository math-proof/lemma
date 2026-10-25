/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericPolygonReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonPerturbation.Part4


namespace StatMech.FrontierA

open scoped Convex

open Set

structure KWPolygonPerturbationCertificate
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) where
  radius : ℝ
  radius_pos : 0 < radius
  rawSimple : ∀ vertex : Fin n → ℂ,
    dist vertex polygon.vertex < radius → KWRawSimplePolygonData vertex


end StatMech.FrontierA
