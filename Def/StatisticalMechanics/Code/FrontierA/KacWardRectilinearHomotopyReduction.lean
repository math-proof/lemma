/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearHomotopyReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleHomotopy.Part3
import Structure.StatisticalMechanics.Code.FrontierA.KacWardRectilinearHomotopyReduction


namespace StatMech.FrontierA

open scoped BigOperators

open Set

open StatMech.Onsager.BaseCase

def KWFiniteSimplePolygonRectilinearizable : Prop :=
  ∀ {n : ℕ} [NeZero n] (source : KWFiniteSimplePolygon n),
    ∃ m : ℕ, ∃ inst : NeZero m,
      Nonempty (@KWRectilinearPhaseHomotopy n m _ inst source)


end StatMech.FrontierA
