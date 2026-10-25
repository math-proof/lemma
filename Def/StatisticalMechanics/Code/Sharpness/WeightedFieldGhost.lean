/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.HcovAssembly.Part4
open Finset BigOperators SimpleGraph
open scoped symmDiff Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Sharpness

namespace WeightedFieldGhost

open StatMech.Ising

open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def weightedEnergy (J : Sym2 V -> ℝ) (h : ℝ) (s : ConfigSpace V) : ℝ :=
  (∑ e ∈ G.edgeFinset, J e * bond s e) + h * ∑ x, spin s x


noncomputable def weightedWeight (β : ℝ) (J : Sym2 V -> ℝ) (h : ℝ)
    (s : ConfigSpace V) : ℝ :=
  Real.exp (β * weightedEnergy G J h s)


noncomputable def weightedZ (β : ℝ) (J : Sym2 V -> ℝ) (h : ℝ) : ℝ :=
  ∑ s : ConfigSpace V, weightedWeight G β J h s


noncomputable def weightedExpectation (β : ℝ) (J : Sym2 V -> ℝ) (h : ℝ)
    (f : ConfigSpace V -> ℝ) : ℝ :=
  (∑ s : ConfigSpace V, f s * weightedWeight G β J h s) / weightedZ G β J h

end WeightedFieldGhost
end Sharpness
end StatMech
