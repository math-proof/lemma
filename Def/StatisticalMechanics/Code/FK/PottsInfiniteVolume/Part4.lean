/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part11
import Theorem.StatisticalMechanics.Code.IsingFK.EsLatticeBridge
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part4
open MeasureTheory Filter Topology TopologicalSpace
open scoped BigOperators ENNReal


namespace StatMech

namespace FK

open Lattice


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


namespace Wired

open IsingFK

variable (bdry : V → Prop) [DecidablePred bdry]


noncomputable def ivp_wiredJointPMF {q : ℕ} [NeZero q]
    (b : Fin q) (beta J : ℝ) (hp : 0 ≤ 1 - Real.exp (-(beta * J))) :
    PMF ((V → Fin q) × ConfigSpace (Sym2 V)) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (ivp_wiredJointProb G bdry b beta J z)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg
        (fun z _ => ivp_wiredJointProb_nonneg G bdry b beta J hp z),
      ivp_wiredJointProb_sum_eq_one G bdry b beta J, ENNReal.ofReal_one]


end Wired
end FK
end StatMech
