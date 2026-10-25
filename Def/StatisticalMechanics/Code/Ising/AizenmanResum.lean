/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean -/

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
import Theorem.StatisticalMechanics.Code.Ising.AizenmanInclusionExclusion.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanHdom.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanResum
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

open StatMech.Sharpness.RandomCurrent


local notation "srcK" => StatMech.Sharpness.RandomCurrent.sources

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


noncomputable def ght_backbones (ends : ι → Sym2 V) (m : Finset ι) (x y : V) : Finset (Finset ι) :=
  m.powerset.filter (fun P => srcK ends P = {x, y})


noncomputable def ght_resummedNoneMass (ends : ι → Sym2 V) (m : Finset ι) (φ : Finset ι → ℝ)
    (A : Finset V) (o x y : V) : ℝ :=
  ∑ P ∈ (ght_backbones ends m x y).filter (fun P => aie_noneConn ends (m ∆ P) o x y),
    aie_mass ends (m ∆ P) φ (A ∆ {x, y})


def ght_backboneAvgDom (ends : ι → Sym2 V) (M : Finset (Finset ι)) (A : Finset V)
    (o x y : V) (Φ : Finset ι → Finset ι → ℝ) : Prop :=
  2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)
    ≤ ∑ m ∈ M.filter (fun m => aie_allConn ends m o x y),
        ght_resummedNoneMass ends m (Φ m) A o x y


end Ising
end StatMech
