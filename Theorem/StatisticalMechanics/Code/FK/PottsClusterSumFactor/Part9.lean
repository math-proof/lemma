/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Def.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part9
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


theorem pottsIIDLabelMeasure_pottsLabelSumEvent
    {d q : Nat} [NeZero q] (F : Finset (Site d)) (hF : F.Nonempty)
    (a : Fin q) :
    pottsIIDLabelMeasure d q (pottsLabelSumEvent F a) =
      (q : ENNReal)⁻¹ := by
  letI : Nonempty F := by
    obtain ⟨x, hx⟩ := hF
    exact ⟨⟨x, hx⟩⟩
  unfold pottsIIDLabelMeasure pottsLabelSumEvent
  calc
    (Measure.infinitePi fun _ : Site d =>
        (PMF.uniformOfFintype (Fin q)).toMeasure)
        (cylinder F {label | ∑ x, label x = a}) =
      Measure.pi (fun _ : F =>
        (PMF.uniformOfFintype (Fin q)).toMeasure)
        {label | ∑ x, label x = a} :=
      Measure.infinitePi_cylinder
        (fun _ : Site d => (PMF.uniformOfFintype (Fin q)).toMeasure)
        (Set.toFinite {label : F -> Fin q | ∑ x, label x = a} |>.measurableSet)
    _ = (q : ENNReal)⁻¹ := pottsUniformPi_sum_apply a


theorem pottsClusterSumSpin_representatives_law
    {d q : Nat} [NeZero q] {κ : Type*}
    (boundaryColor : Fin q) (omega : ConfigSpace (Sym2 (Site d)))
    (r : κ -> Site d)
    (hfinite : ∀ k, (cluster d omega (r k)).Finite)
    (hdistinct : ∀ k l, k ≠ l -> ¬Connected d omega (r k) (r l)) :
    Measure.map (fun label k =>
        pottsClusterSumSpin boundaryColor omega label (r k))
        (pottsIIDLabelMeasure d q) =
      Measure.infinitePi fun _ : κ =>
        (PMF.uniformOfFintype (Fin q)).toMeasure := by
  let F : κ -> Finset (Site d) := fun k => (hfinite k).toFinset
  have hF : ∀ k, (F k).Nonempty := by
    intro k
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hself : r k ∈ F k := by
      change r k ∈ (hfinite k).toFinset
      simpa only [Set.Finite.mem_toFinset] using self_mem_cluster omega (r k)
    simpa [hempty] using hself
  have hdisjoint : ∀ k l, k ≠ l -> Disjoint (F k) (F l) := by
    intro k l hne
    apply Finset.disjoint_left.mpr
    intro z hzk hzl
    have hzk' : z ∈ cluster d omega (r k) := by
      simpa [F] using hzk
    have hzl' : z ∈ cluster d omega (r l) := by
      simpa [F] using hzl
    apply hdistinct k l hne
    exact (mem_cluster.mp hzk').trans (mem_cluster.mp hzl').symm
  have hfactor : (fun label k =>
        pottsClusterSumSpin boundaryColor omega label (r k)) =
      pottsBlockSums F := by
    funext label k
    rw [pottsClusterSumSpin_of_finite boundaryColor omega label (r k) (hfinite k)]
    exact Finset.sum_subtype (F k) (fun _ => Iff.rfl) label
  rw [hfactor]
  exact pottsIID_blockSums_law F hF hdisjoint

end StatMech.FK
