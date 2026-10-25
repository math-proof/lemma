/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIntersectionUnionBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourCurrentTree
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianIntersectionUnionBound
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem finiteTreeSeparatedFourMass_eq_summand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l y : V) :
    finiteTreeSeparatedFourMass G beta J i j k l y =
      ∑' z : TreeFourProfiles G,
        finiteTreeSeparatedFourSummand G beta J i j k l y z := by
  unfold finiteTreeSeparatedFourMass
  apply tsum_congr
  rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rfl

end StatMech.FrontierA
