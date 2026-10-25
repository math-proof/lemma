/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.EvenSubgraphDecomp
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenPeel.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardStar.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising


noncomputable instance kwStarGraph_decidableAdj {ι : Type*} :
    DecidableRel (kwStarGraph ι).Adj := Classical.decRel _


end StatMech.FrontierA
