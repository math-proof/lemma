/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterfly
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerFiberClose.Part2
import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBetaSum
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInhom.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldPercoInhom.Part2
open Finset SimpleGraph Set


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def mpiPhi (beta : ℝ) (J : Sym2 V → ℝ)
    (o : V) (S : Finset V) : ℝ :=
  ∑ q ∈ shk_boundaryPairs G S,
    (1 - Real.exp (-beta * J s(q.1, q.2))) *
      wprob (shk_edgeLaw beta J) (connEvent G (S : Set V) o {q.1})


end Sharpness
end StatMech
