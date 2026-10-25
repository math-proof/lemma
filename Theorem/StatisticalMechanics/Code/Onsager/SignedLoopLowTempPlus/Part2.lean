/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempPlus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempCorrelation.Part2
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Def.StatisticalMechanics.Code.Onsager.SignedLoopLowTempPlus.Part2
open scoped BigOperators
open Finset SimpleGraph MeasureTheory


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Walls


theorem ons_plusLowTempPathSign_eq_spin_mul {d : Nat}
    (config : ConfigSpace (Site d)) {u v : Site d}
    (path : (hypercubicLattice d).Walk u v) :
    ons_plusLowTempPathSign config path = spin config u * spin config v := by
  unfold ons_plusLowTempPathSign
  have hpar := kwd_crossCount_parity config path
  by_cases hsame : config u = config v
  · rw [if_pos (hpar.mpr hsame)]
    cases hu : config u <;> cases hv : config v <;>
      simp_all [spin]
  · rw [if_neg (fun heven => hsame (hpar.mp heven))]
    cases hu : config u <;> cases hv : config v <;>
      simp_all [spin]


end StatMech.Onsager
