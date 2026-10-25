/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumContinuity.Part2
import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part8
import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteMultipointES
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part5
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem measurable_boxClusterSumJointFactor
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (n : Nat) :
    Measurable (boxClusterSumJointFactor (d := d) boundaryColor n) := by
  have hembed : Measurable (fun input :
      ConfigSpace (Sym2 (boxVerts d n)) × (Site d -> Fin q) =>
      (extendEdge d n input.1, input.2)) :=
    ((measurable_extendEdge d n).comp measurable_fst).prodMk measurable_snd
  have hfactor := (measurable_pottsClusterSumJointFactor boundaryColor).comp hembed
  have heq : boxClusterSumJointFactor (d := d) boundaryColor n =
      pottsBoxJointRestrict d n q ∘
        pottsClusterSumJointFactor boundaryColor ∘
          (fun input => (extendEdge d n input.1, input.2)) := by
    funext input
    apply Prod.ext
    · rfl
    · funext e
      exact (extendEdge_eq_of_range n e input.1).symm
  rw [heq]
  exact (measurable_pottsBoxJointRestrict d n q).comp hfactor

theorem pottsBoxJointRestrict_clusterFactor_extendEdge
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (n : Nat)
    (input : ConfigSpace (Sym2 (boxVerts d n)) × (Site d -> Fin q)) :
    pottsBoxJointRestrict d n q
        (pottsClusterSumJointFactor boundaryColor
          (extendEdge d n input.1, input.2)) =
      boxClusterSumJointFactor boundaryColor n input := by
  apply Prod.ext
  · rfl
  · funext e
    exact extendEdge_eq_of_range n e input.1


theorem freePottsJointFiniteMeasure_map_boxRestrict
    (d n q : Nat) [NeZero q] (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    (freePottsJointFiniteMeasure d n q beta J hp hp1).map
        (measurable_pottsBoxJointRestrict d n q).aemeasurable =
      ⟨(ivp_freeJointPMF (boxGraph d n) q hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : Real) < q)).toMeasure,
        inferInstance⟩ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (pottsBoxJointRestrict d n q)
      (Measure.map (ivp_extendJoint d n q)
        (ivp_freeJointPMF (boxGraph d n) q hp hp1
          (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : Real) < q)).toMeasure) = _
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
  change (ivp_freeJointPMF (boxGraph d n) q hp hp1 _).toMeasure =
    (ivp_freeJointPMF (boxGraph d n) q hp hp1 _).toMeasure
  rfl


theorem freeESJointFiniteMeasure_map_boxRestrict
    (d n q : Nat) [NeZero q] {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : Real)) :
    (freeESJointFiniteMeasure d n q hp hp1 hq).map
        (measurable_pottsBoxJointRestrict d n q).aemeasurable =
      ⟨(ivp_freeJointPMF (boxGraph d n) q hp hp1 hq).toMeasure,
        inferInstance⟩ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (pottsBoxJointRestrict d n q)
      (Measure.map (ivp_extendJoint d n q)
        (ivp_freeJointPMF (boxGraph d n) q hp hp1 hq).toMeasure) = _
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
  change (ivp_freeJointPMF (boxGraph d n) q hp hp1 hq).toMeasure =
    (ivp_freeJointPMF (boxGraph d n) q hp hp1 hq).toMeasure
  rfl

set_option maxHeartbeats 3000000 in


theorem pottsClusterSumJointProbabilityMeasure_freeFinite_map_boxRestrict
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (n : Nat) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : Real)) :
    (pottsClusterSumJointProbabilityMeasure boundaryColor
        (freeFiniteMeasure d n hp hp1 hq)).map
        (measurable_pottsBoxJointRestrict d n q).aemeasurable =
      ⟨(ivp_freeJointPMF (boxGraph d n) q hp hp1 hq).toMeasure,
        inferInstance⟩ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (pottsBoxJointRestrict d n q)
      (Measure.map (pottsClusterSumJointFactor boundaryColor)
        ((Measure.map (extendEdge d n)
          (fkPMF (boxGraph d n) hp hp1 hq).toMeasure).prod
            (pottsIIDLabelMeasure d q))) = _
  rw [Measure.map_map (measurable_pottsBoxJointRestrict d n q)
    (measurable_pottsClusterSumJointFactor boundaryColor)]
  have hprod :
      (Measure.map (extendEdge d n)
          (fkPMF (boxGraph d n) hp hp1 hq).toMeasure).prod
          (pottsIIDLabelMeasure d q) =
        Measure.map (Prod.map (extendEdge d n) id)
          ((fkPMF (boxGraph d n) hp hp1 hq).toMeasure.prod
            (pottsIIDLabelMeasure d q)) := by
    have hid : Measure.map id (pottsIIDLabelMeasure d q) =
        pottsIIDLabelMeasure d q := Measure.map_id
    calc
      (Measure.map (extendEdge d n)
          (fkPMF (boxGraph d n) hp hp1 hq).toMeasure).prod
          (pottsIIDLabelMeasure d q) =
        (Measure.map (extendEdge d n)
          (fkPMF (boxGraph d n) hp hp1 hq).toMeasure).prod
          (Measure.map id (pottsIIDLabelMeasure d q)) := by rw [hid]
      _ = _ := Measure.map_prod_map
        (fkPMF (boxGraph d n) hp hp1 hq).toMeasure
        (pottsIIDLabelMeasure d q)
        (measurable_extendEdge d n) measurable_id
  rw [hprod, Measure.map_map]
  · have hcomp :
        (pottsBoxJointRestrict d n q ∘
            pottsClusterSumJointFactor boundaryColor) ∘
            Prod.map (extendEdge d n) id =
          boxClusterSumJointFactor (d := d) boundaryColor n := by
      funext input
      exact pottsBoxJointRestrict_clusterFactor_extendEdge
        boundaryColor n input
    rw [hcomp, ← freeClusterColorJointPMF_eq_ivp_freeJointPMF
      (boxGraph d n) q hp hp1 hq]
    apply Measure.ext_of_singleton
    rintro ⟨sigma, omegaTarget⟩
    have hsingle : MeasurableSet
        ({(sigma, omegaTarget)} : Set
          ((boxVerts d n -> Fin q) × ConfigSpace (Sym2 (boxVerts d n)))) :=
      MeasurableSet.of_discrete
    rw [Measure.map_apply (measurable_boxClusterSumJointFactor (d := d) boundaryColor n)
      hsingle]
    rw [Measure.prod_apply
      ((hsingle.preimage
        (measurable_boxClusterSumJointFactor (d := d) boundaryColor n)))]
    rw [lintegral_fintype]
    change (∑ x,
        (pottsIIDLabelMeasure d q)
          (Prod.mk x ⁻¹' boxClusterSumJointFactor (d := d) boundaryColor n ⁻¹'
            {(sigma, omegaTarget)}) *
          (fkPMF (boxGraph d n) hp hp1 hq).toMeasure {x}) =
      (freeClusterColorJointPMF (boxGraph d n) q hp hp1 hq).toMeasure
        {(sigma, omegaTarget)}
    rw [PMF.toMeasure_apply_singleton _ _ hsingle]
    unfold freeClusterColorJointPMF
    rw [PMF.bind_apply, tsum_fintype]
    have hspinMeas : Measurable (fun label : Site d -> Fin q =>
        fun x : boxVerts d n => pottsClusterSumSpin boundaryColor
          (extendEdge d n omegaTarget) label (x : Site d)) := by
      exact measurable_pi_lambda _ fun x =>
        (measurable_pottsClusterSumSpin_apply boundaryColor (x : Site d)).comp
          (measurable_const.prodMk measurable_id)
    have hsigma : MeasurableSet ({sigma} : Set (boxVerts d n -> Fin q)) :=
      MeasurableSet.of_discrete
    have hcond :
        (pottsIIDLabelMeasure d q)
            {label | (fun x : boxVerts d n =>
              pottsClusterSumSpin boundaryColor (extendEdge d n omegaTarget)
                label (x : Site d)) = sigma} =
          ((PMF.uniformOfFintype
            ((openSub (boxGraph d n) omegaTarget).ConnectedComponent -> Fin q)).map
              (IsingFK.coloring (boxGraph d n) omegaTarget)) sigma := by
      calc
        (pottsIIDLabelMeasure d q)
            {label | (fun x : boxVerts d n =>
              pottsClusterSumSpin boundaryColor (extendEdge d n omegaTarget)
                label (x : Site d)) = sigma} =
            Measure.map (fun label (x : boxVerts d n) =>
              pottsClusterSumSpin boundaryColor (extendEdge d n omegaTarget)
                label (x : Site d)) (pottsIIDLabelMeasure d q) {sigma} := by
              rw [Measure.map_apply hspinMeas hsigma]
              rfl
        _ = ((PMF.uniformOfFintype
              ((openSub (boxGraph d n) omegaTarget).ConnectedComponent -> Fin q)).map
                (IsingFK.coloring (boxGraph d n) omegaTarget)).toMeasure
                  {sigma} := by
              rw [boxClusterSumSpin_law boundaryColor n omegaTarget]
        _ = ((PMF.uniformOfFintype
              ((openSub (boxGraph d n) omegaTarget).ConnectedComponent -> Fin q)).map
                (IsingFK.coloring (boxGraph d n) omegaTarget)) sigma := by
              rw [PMF.toMeasure_apply_singleton _ _ hsigma]
    have hsourcePoint :
        (fkPMF (boxGraph d n) hp hp1 hq).toMeasure {omegaTarget} =
          fkPMF (boxGraph d n) hp hp1 hq omegaTarget :=
      PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete
    have hsum : (∑ omega : ConfigSpace (Sym2 (boxVerts d n)),
        (pottsIIDLabelMeasure d q)
            (Prod.mk omega ⁻¹'
              (boxClusterSumJointFactor boundaryColor n ⁻¹'
                {(sigma, omegaTarget)})) *
          (fkPMF (boxGraph d n) hp hp1 hq).toMeasure {omega}) =
        (pottsIIDLabelMeasure d q)
            {label | (fun x : boxVerts d n =>
              pottsClusterSumSpin boundaryColor (extendEdge d n omegaTarget)
                label (x : Site d)) = sigma} *
          fkPMF (boxGraph d n) hp hp1 hq omegaTarget := by
      rw [Finset.sum_eq_single omegaTarget]
      · rw [hsourcePoint]
        have hsets : Prod.mk omegaTarget ⁻¹'
            (boxClusterSumJointFactor boundaryColor n ⁻¹'
              {(sigma, omegaTarget)}) =
            {label | (fun x : boxVerts d n =>
              pottsClusterSumSpin boundaryColor (extendEdge d n omegaTarget)
                label (x : Site d)) = sigma} := by
          apply Set.ext
          intro label
          simp [boxClusterSumJointFactor]
        rw [hsets]
      · intro omega _ hne
        have hempty : Prod.mk omega ⁻¹'
            (boxClusterSumJointFactor boundaryColor n ⁻¹'
              {(sigma, omegaTarget)}) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro label hlabel
          have heq : boxClusterSumJointFactor boundaryColor n (omega, label) =
              (sigma, omegaTarget) := hlabel
          exact hne (congrArg Prod.snd heq)
        rw [hempty, measure_empty, zero_mul]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    rw [hsum, hcond]
    rw [Finset.sum_eq_single omegaTarget]
    · simp only [PMF.map_apply]
      rw [mul_comm]
      congr 1
      apply tsum_congr
      intro labels
      by_cases heq : sigma = IsingFK.coloring (boxGraph d n) omegaTarget labels
      · simp [heq]
      · simp [heq]
    · intro omega _ hne
      have hmap0 :
          ((PMF.uniformOfFintype
            ((openSub (boxGraph d n) omega).ConnectedComponent -> Fin q)).map
              (fun tau => (IsingFK.coloring (boxGraph d n) omega tau, omega)))
              (sigma, omegaTarget) = 0 := by
        rw [PMF.map_apply, tsum_fintype]
        apply Finset.sum_eq_zero
        intro tau _
        simp only [ite_eq_right_iff]
        intro heq
        exact (hne (congrArg Prod.snd heq).symm).elim
      simp only [hmap0, mul_zero]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · exact (measurable_pottsBoxJointRestrict d n q).comp
      (measurable_pottsClusterSumJointFactor boundaryColor)
  · exact ((measurable_extendEdge d n).comp measurable_fst).prodMk
      measurable_snd


theorem isClopen_pottsSpinCylinder
    {d q : Nat} (s : Finset (Site d))
    (S : Set (∀ _x : s, Fin q)) :
    IsClopen (cylinder (α := fun _ : Site d => Fin q) s S) := by
  apply IsClopen.preimage
  · exact isClopen_discrete S
  · exact continuous_pi fun x => continuous_apply x.1


end StatMech.FK
