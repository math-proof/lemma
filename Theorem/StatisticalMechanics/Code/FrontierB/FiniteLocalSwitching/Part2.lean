/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentPairCylinders.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete.Part4
import Def.StatisticalMechanics.Code.FrontierB.FiniteLocalSwitching.Part2
open scoped symmDiff


namespace StatMech.FrontierB

open Sharpness

open Finset MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable {E : Type*} [Countable E]

omit [Countable E] in
theorem isClopen_currentSuperpositionCylinder (S : Finset E)
    (A : Set (↑S → ℕ)) :
    IsClopen (currentSuperpositionCylinder S A) :=
  isClopen_currentPairCylinder S _

theorem WeakCurrentConverges.superpositionCylinder
    {mu nu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {muLim nuLim : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (hmu : WeakCurrentConverges mu muLim)
    (hnu : WeakCurrentConverges nu nuLim)
    (S : Finset E) (A : Set (↑S → ℕ)) :
    Filter.Tendsto
      (fun k => (mu k).prod (nu k) (currentSuperpositionCylinder S A))
      Filter.atTop
      (nhds (muLim.prod nuLim (currentSuperpositionCylinder S A))) :=
  hmu.pairCylinder hnu S _

end StatMech.FrontierB
