/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFiniteCurrentUrsell.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFourCurrent
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedSurvivorSwitching
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianFiniteCurrentUrsell
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem finiteIsingFourthUrsell_eq_current
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) :
    finiteIsingFourthUrsell G beta J i j k l =
      finiteCurrentFourthUrsell G beta J i j k l := by
  unfold finiteIsingFourthUrsell finiteCurrentFourthUrsell
  dsimp only
  simp_rw [current_representation]
  have hZ : currentSum G beta J ∅ ≠ 0 :=
    ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos G beta J)
  field_simp [hZ]


end StatMech.FrontierA
