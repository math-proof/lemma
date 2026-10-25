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
import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part7
open MeasureTheory Filter Topology TopologicalSpace
open scoped BigOperators ENNReal


namespace StatMech

namespace FK

open Lattice


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def freePottsFiniteMeasure (d n q : ℕ) [NeZero q]
    (beta J : ℝ) : ProbabilityMeasure (PottsConfig d q) :=
  ⟨(Potts.pottsPMF (boxGraph d n) q beta J).toMeasure.map (ivp_extendSpin d n q),
    inferInstance⟩


noncomputable def freePottsJointFiniteMeasure (d n q : ℕ) [NeZero q]
    (beta J : ℝ)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    ProbabilityMeasure (PottsJointConfig d q) :=
  ⟨(ivp_freeJointPMF (boxGraph d n) q hp hp1
      (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).toMeasure.map
        (ivp_extendJoint d n q),
    inferInstance⟩


noncomputable def wiredPottsPMF (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V → Prop) [DecidablePred bdry] (q : ℕ) [NeZero q]
    (b : Fin q) (beta J : ℝ) : PMF (V → Fin q) :=
  PMF.ofFintype
    (fun s => ENNReal.ofReal (IsingFK.pottsProbWired G bdry q b beta J s)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg
          (fun s _ => IsingFK.pottsProbWired_nonneg G bdry q b beta J s),
        IsingFK.pottsProbWired_sum_eq_one G bdry q b beta J, ENNReal.ofReal_one])


noncomputable def wiredPottsFiniteMeasure (d n q : ℕ) [NeZero q]
    (b : Fin q) (beta J : ℝ) : ProbabilityMeasure (PottsConfig d q) :=
  ⟨(wiredPottsPMF (boxGraph d n) (boxBoundary d n) q b beta J).toMeasure.map
      (ivp_extendSpin d n q),
    inferInstance⟩


noncomputable def wiredPottsJointFiniteMeasure (d n q : ℕ) [NeZero q]
    (b : Fin q) (beta J : ℝ)
    (hp : 0 ≤ 1 - Real.exp (-(beta * J))) :
    ProbabilityMeasure (PottsJointConfig d q) :=
  ⟨(Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n) b beta J hp).toMeasure.map
      (ivp_extendJoint d n q),
    inferInstance⟩


end FK
end StatMech
