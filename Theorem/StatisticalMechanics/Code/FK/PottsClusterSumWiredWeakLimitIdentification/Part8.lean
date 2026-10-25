/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part6
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.FreeDLRExtreme
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredWeakLimitIdentification.Part8
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


namespace Wired

open IsingFK

variable (bdry : V -> Prop) [DecidablePred bdry]


theorem clusterColorJointPMF_eq_ivp_wiredJointPMF
    {q : Nat} [NeZero q] (b : Fin q) (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1)
    (v0 : V) (hv0 : bdry v0) :
    clusterColorJointPMF G bdry b beta J hp hp1 =
      ivp_wiredJointPMF G bdry b beta J hp.le := by
  classical
  ext z
  rcases z with ⟨sigma, omega⟩
  rw [clusterColorJointPMF, PMF.bind_apply, tsum_fintype,
    Finset.sum_eq_single omega]
  · simp only [PMF.map_apply, Prod.mk.injEq, and_true]
    have hpair : (∑' tau : V -> Fin q,
        if sigma = tau then conditionalClusterColorPMF G bdry b omega tau else 0) =
        conditionalClusterColorPMF G bdry b omega sigma := by
      rw [tsum_eq_single sigma]
      · simp
      · intro tau hne
        rw [if_neg]
        exact Ne.symm hne
    rw [hpair, conditionalClusterColorPMF_apply]
    simp only [ivp_wiredJointPMF, PMF.ofFintype_apply, wiredFkPMF,
      PMF.ofFintype_apply]
    rw [ivp_wiredJointProb_eq_wiredFkProb_div_card G bdry b beta J hp hp1
      v0 hv0 sigma omega]
    by_cases hcompat : ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma
    · rw [dif_pos hcompat, if_pos hcompat]
      rw [ENNReal.ofReal_div_of_pos]
      · simp only [ENNReal.ofReal_natCast, div_eq_mul_inv]
      · exact_mod_cast compatibleBoundarySpin_card_pos G bdry b omega
    · simp [hcompat]
  · intro omega' _ hne
    simp [hne, Ne.symm hne]
  · simp


theorem wiredPottsJointFiniteMeasure_map_boxRestrict
    (d n q : Nat) [NeZero q] (b : Fin q) (beta J : Real)
    (hp : 0 ≤ 1 - Real.exp (-(beta * J))) :
    (wiredPottsJointFiniteMeasure d n q b beta J hp).map
        (measurable_pottsBoxJointRestrict d n q).aemeasurable =
      ⟨(ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
          b beta J hp).toMeasure, inferInstance⟩ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (pottsBoxJointRestrict d n q)
      (Measure.map (ivp_extendJoint d n q)
        (ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
          b beta J hp).toMeasure) = _
  rw [Measure.map_map (measurable_pottsBoxJointRestrict d n q)
    (ivp_measurable_extendJoint d n q)]
  have hleft : pottsBoxJointRestrict d n q ∘ ivp_extendJoint d n q = id := by
    funext z
    apply Prod.ext
    · funext x
      simp [pottsBoxJointRestrict, ivp_extendJoint, ivp_extendSpin, x.2]
    · funext e
      exact extendEdge_eq_of_range n e z.2
  rw [hleft, Measure.map_id]
  rfl


end Wired
end StatMech.FK
