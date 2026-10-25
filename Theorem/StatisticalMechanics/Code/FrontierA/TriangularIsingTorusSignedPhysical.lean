/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSignedPhysical
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem two_mul_triangularTorus_spinCharacter_eq_walsh
    (a b : Fin 2) (h : Fin 2 × Fin 2) :
    2 * ons_spinCharacter a b h =
      ∑ chi : Fin 2 × Fin 2,
        triangularTorusQuadraticWalshSign a b chi *
          triangularTorusLinearCharacter chi h := by
  rcases h with ⟨h1, h2⟩
  fin_cases a <;> fin_cases b <;> fin_cases h1 <;> fin_cases h2 <;>
    norm_num [ons_spinCharacter, triangularTorusQuadraticWalshSign,
      triangularTorusLinearCharacter, Fintype.sum_prod_type,
      Fin.sum_univ_two]


end StatMech.FrontierA
