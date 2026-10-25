/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanDecompFull.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

namespace AizenmanDecomp

open StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


noncomputable def aid_mass (ends : ι → Sym2 V) (m : Finset ι) (φ : Finset ι → ℝ) (S : Finset V) :
    ℝ :=
  ∑ K ∈ m.powerset.filter (fun K => Sharpness.RandomCurrent.sources ends K = S), φ K


noncomputable def aid_gap (ends : ι → Sym2 V) (m : Finset ι) (φ : Finset ι → ℝ) (A : Finset V)
    (o x y : V) : ℝ :=
  aid_mass ends m φ A - aid_mass ends m φ (A ∆ {x, y})
    - aid_mass ends m φ (A ∆ {o, y}) - aid_mass ends m φ (A ∆ {o, x})


end AizenmanDecomp
end Ising
end StatMech
