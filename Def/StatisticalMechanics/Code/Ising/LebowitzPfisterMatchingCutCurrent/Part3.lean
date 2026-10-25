/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterMatchingCutCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostVarianceSector
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterMatchingCutCurrent.Part2
open Finset
open scoped BigOperators symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W I : Type*} [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]


noncomputable def lpMatchingFiveCurrentCoefficient
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) (i j : I) : Real :=
  let Si := lpMatchingSeamSource left right i
  let Sj := lpMatchingSeamSource left right j
  let T := lpMatchingGhostSource g0 g1
  lpFiveCurrentSourceMass G beta J (Si ∆ Sj ∆ T) ∅ ∅ ∅ ∅ -
    lpFiveCurrentSourceMass G beta J (Si ∆ Sj) T ∅ ∅ ∅ -
    2 * lpFiveCurrentSourceMass G beta J Si (Sj ∆ T) ∅ ∅ ∅ +
    2 * lpFiveCurrentSourceMass G beta J Si Sj T ∅ ∅ -
    lpFiveCurrentSourceMass G beta J (Si ∆ Sj ∆ T) T T ∅ ∅ +
    lpFiveCurrentSourceMass G beta J (Si ∆ Sj) T T T ∅ -
    2 * lpFiveCurrentSourceMass G beta J Si (Sj ∆ T) T T ∅ +
    2 * lpFiveCurrentSourceMass G beta J (Si ∆ T) (Sj ∆ T) T ∅ ∅


def lpFiveSourceTotal
    (S1 S2 S3 S4 S5 : Finset W) : Finset W :=
  S1 ∆ S2 ∆ S3 ∆ S4 ∆ S5


end
end StatMech.Ising
