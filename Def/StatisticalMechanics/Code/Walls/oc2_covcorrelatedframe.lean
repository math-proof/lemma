/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Theorem.StatisticalMechanics.Code.Walls.oc_core.Part3
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.MonotonicMeasure

open StatMech.OSSS.MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def oc2_meanCorr (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  genMean (fkMass G p q) g


noncomputable def oc2_covCorr (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  genCov (fkMass G p q) f g


noncomputable def oc2_coordRead (e : Sym2 V) : ConfigSpace (Sym2 V) → ℝ :=
  (genCoord e : ConfigSpace (Sym2 V) → ℝ)


end Walls
end StatMech
