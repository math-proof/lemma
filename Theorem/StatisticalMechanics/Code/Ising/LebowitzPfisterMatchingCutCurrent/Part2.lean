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
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterMatchingCutCurrent.Part2
open Finset
open scoped BigOperators symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W I : Type*} [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]


theorem lpFiveCurrentSourceMass_eq_sourceTriple_mul_sourcePair
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (S1 S2 S3 S4 S5 : Finset W) :
    lpFiveCurrentSourceMass G beta J S1 S2 S3 S4 S5 =
      sourceTripleSum G beta J S1 S2 S3 *
        sourcePairSum G beta J S4 S5 := by
  rw [sourceTripleSum_eq_mul, sourcePairSum_eq_mul]
  unfold lpFiveCurrentSourceMass
  ring


end
end StatMech.Ising
