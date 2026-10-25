/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness


noncomputable def inhomogeneousFiniteParityPMF
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (hlambda : forall e : S, 0 < lambda e.1) (odd : S -> Bool) :
    PMF (S -> Nat) :=
  PMF.normalize
    (fun a => ENNReal.ofReal
      (inhomogeneousFiniteParityKernel S lambda odd a))
    (by
      rw [tsum_ofReal_inhomogeneousFiniteParityKernel S lambda hlambda odd]
      exact one_ne_zero)
    (by
      rw [tsum_ofReal_inhomogeneousFiniteParityKernel S lambda hlambda odd]
      exact ENNReal.one_ne_top)

end StatMech.FrontierB
