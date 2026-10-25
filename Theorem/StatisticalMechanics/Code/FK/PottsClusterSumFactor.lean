/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Def.StatisticalMechanics.Code.FK.PottsClusterSumFactor
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


theorem pottsClusterSumSpin_eq_of_connected {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (omega : ConfigSpace (Sym2 (Site d)))
    (label : Site d -> Fin q) {x y : Site d}
    (hxy : Connected d omega x y) :
    pottsClusterSumSpin boundaryColor omega label x =
      pottsClusterSumSpin boundaryColor omega label y := by
  classical
  unfold pottsClusterSumSpin
  rw [cluster_eq_of_connected hxy]


theorem pottsClusterSumSpin_constOnOpen {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (omega : ConfigSpace (Sym2 (Site d)))
    (label : Site d -> Fin q) :
    ConstOnOpen (hypercubicLattice d) omega
      (pottsClusterSumSpin boundaryColor omega label) := by
  intro x y hxy
  exact pottsClusterSumSpin_eq_of_connected boundaryColor omega label
    hxy.reachable


theorem pottsClusterSumSpin_of_infinite {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (omega : ConfigSpace (Sym2 (Site d)))
    (label : Site d -> Fin q) (x : Site d)
    (hinfinite : (cluster d omega x).Infinite) :
    pottsClusterSumSpin boundaryColor omega label x = boundaryColor := by
  classical
  rw [pottsClusterSumSpin, dif_neg hinfinite]


theorem pottsClusterSumSpin_of_finite {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (omega : ConfigSpace (Sym2 (Site d)))
    (label : Site d -> Fin q) (x : Site d)
    (hfinite : (cluster d omega x).Finite) :
    pottsClusterSumSpin boundaryColor omega label x =
      ∑ y ∈ hfinite.toFinset, label y := by
  classical
  rw [pottsClusterSumSpin, dif_pos hfinite]


theorem pottsClusterSumSpin_shift {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (g : Multiplicative (Site d))
    (omega : ConfigSpace (Sym2 (Site d))) (label : Site d -> Fin q)
    (x : Site d) :
    pottsClusterSumSpin boundaryColor (ConfigSpace.shift g omega)
        (pottsLabelShift g label) (g • x) =
      pottsClusterSumSpin boundaryColor omega label x := by
  classical
  rw [pottsClusterSumSpin, pottsClusterSumSpin, cluster_shift]
  by_cases hfinite : (cluster d omega x).Finite
  · have himage : ((fun y => g • y) '' cluster d omega x).Finite :=
      hfinite.image _
    rw [dif_pos himage, dif_pos hfinite]
    rw [Set.Finite.toFinset_image (fun y => g • y) hfinite himage]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro y hy
      simp [pottsLabelShift]
    · intro a ha b hb hab
      exact smul_left_cancel g hab
  · have himage : ¬((fun y => g • y) '' cluster d omega x).Finite := by
      intro h
      apply hfinite
      have hpre : cluster d omega x =
          (fun y => g⁻¹ • y) '' ((fun y => g • y) '' cluster d omega x) := by
        ext y
        simp
      rw [hpre]
      exact h.image _
    rw [dif_neg himage, dif_neg hfinite]


end StatMech.FK
