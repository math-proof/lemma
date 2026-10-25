/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIntersectionUnionBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourCurrentTree
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIntersectionUnionBound
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def finiteTreeFourWeightMajorant
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (z : TreeFourProfiles G) : Real :=
  ‖weight G beta J (ofEdgeFun G z.1.1)‖ *
    ‖weight G beta J (ofEdgeFun G z.1.2)‖ *
    ‖weight G beta J (ofEdgeFun G z.2.1)‖ *
    ‖weight G beta J (ofEdgeFun G z.2.2)‖

end StatMech.FrontierA
