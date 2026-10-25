/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAcyclicElimination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGauge
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13
import Mathlib.Algebra.Ring.GeomSum
open scoped BigOperators


namespace StatMech.FrontierA

open Matrix


theorem kw_fourPort_even_iff_unique_trivalent_completion
    (b0 b1 b2 b3 : Fin 2) :
    b0 + b1 + b2 + b3 = 0 ↔
      ∃! y : Fin 3 -> Fin 2,
        StatMech.Onsager.ons_decChainEven b0 b1 b2 b3 y := by
  constructor
  · exact StatMech.Onsager.ons_decChain_existsUnique b0 b1 b2 b3
  · rintro ⟨y, hy, _⟩
    exact StatMech.Onsager.ons_decChainEven_port_even hy


end StatMech.FrontierA
