/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingLatticeGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSparseGreenDecay
open Filter Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice


theorem isingDyadicTorusGreen_cauchySeq
    {d : Nat} (hd : 2 < d) (x : Site d) :
    CauchySeq (fun k => isingDyadicTorusGreen x k) := by
  rw [Metric.cauchySeq_iff]
  intro epsilon hepsilon
  obtain ⟨eta, heta, hclose⟩ :=
    isingDyadicTorusGreen_eventually_close_continuum
      hd (epsilon / 2) (half_pos hepsilon)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hclose x)
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [Real.dist_eq]
  calc
    |isingDyadicTorusGreen x m - isingDyadicTorusGreen x n| <=
        |isingDyadicTorusGreen x m -
            isingRegularizedContinuumGreen eta x| +
          |isingDyadicTorusGreen x n -
            isingRegularizedContinuumGreen eta x| := by
      calc
        |isingDyadicTorusGreen x m - isingDyadicTorusGreen x n| <=
            |isingDyadicTorusGreen x m -
                isingRegularizedContinuumGreen eta x| +
              |isingRegularizedContinuumGreen eta x -
                isingDyadicTorusGreen x n| := abs_sub_le _ _ _
        _ = _ := by rw [abs_sub_comm
          (isingRegularizedContinuumGreen eta x)
          (isingDyadicTorusGreen x n)]
    _ < epsilon / 2 + epsilon / 2 := add_lt_add (hN m hm) (hN n hn)
    _ = epsilon := by ring


end StatMech.FrontierA
