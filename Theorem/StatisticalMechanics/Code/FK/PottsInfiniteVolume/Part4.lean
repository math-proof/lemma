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
import Def.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part3
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


theorem ivp_esZWired_pos {q : ℕ} [NeZero q] (b : Fin q) (beta J : ℝ) :
    0 < esZWired G bdry q b (1 - Real.exp (-(beta * J))) := by
  rw [esZWired_eq_pottsZWired G bdry b beta J]
  exact mul_pos (esFirstConst_pos G beta J) (pottsZWired_pos G bdry q b beta J)

theorem ivp_wiredJointProb_nonneg {q : ℕ} [NeZero q] (b : Fin q) (beta J : ℝ)
    (hp : 0 ≤ 1 - Real.exp (-(beta * J)))
    (z : (V → Fin q) × ConfigSpace (Sym2 V)) :
    0 ≤ ivp_wiredJointProb G bdry b beta J z := by
  exact div_nonneg
    (esWeightWired_nonneg G bdry hp
      (by linarith [Real.exp_pos (-(beta * J))]) z.1 z.2)
    (ivp_esZWired_pos G bdry b beta J).le

theorem ivp_wiredJointProb_sum_eq_one {q : ℕ} [NeZero q]
    (b : Fin q) (beta J : ℝ) :
    ∑ z : (V → Fin q) × ConfigSpace (Sym2 V),
      ivp_wiredJointProb G bdry b beta J z = 1 := by
  unfold ivp_wiredJointProb
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_div]
  rw [show (∑ s : V → Fin q, ∑ w : ConfigSpace (Sym2 V),
      esWeightWired G bdry b (1 - Real.exp (-(beta * J))) s w) =
      esZWired G bdry q b (1 - Real.exp (-(beta * J))) by
        rw [esZWired, Finset.sum_comm]]
  exact div_self (ivp_esZWired_pos G bdry b beta J).ne'


end Wired
end FK
end StatMech
