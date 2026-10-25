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
import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part2
open MeasureTheory Filter Topology TopologicalSpace
open scoped BigOperators ENNReal


namespace StatMech

namespace FK

open Lattice


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ivp_freeJointPMF (q : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : ℝ)) :
    PMF ((V → Fin q) × ConfigSpace (Sym2 V)) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (ivp_freeJointProb G q p z)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg
        (fun z _ => ivp_freeJointProb_nonneg G hp.le hp1.le z),
      ivp_freeJointProb_sum_eq_one G hp hp1 hq, ENNReal.ofReal_one]


end FK
end StatMech
