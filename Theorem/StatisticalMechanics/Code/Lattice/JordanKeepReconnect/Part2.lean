/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanWindingConstruct.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepDual.Part4
import Def.StatisticalMechanics.Code.Lattice.JordanKeepReconnect.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jkr_finite_of_keepReconnect (hres : jwn_KeepReconnectResidue) :
    jkr_FiniteKeepReconnectResidue :=
  fun H p q f0 g0 _hfin hpq hnpq hfg hshared hnr => hres H p q f0 g0 hpq hnpq hfg hshared hnr


theorem jkr_lineH_edgeSet_infinite : jkr_lineH.edgeSet.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => s(![(n : ℤ) + 1, (0:ℤ)], ![(n : ℤ) + 1 + 1, 0])) ?_ ?_
  · intro m n hmn
    simp only at hmn
    rw [Sym2.eq_iff] at hmn
    rcases hmn with ⟨h, _⟩ | ⟨h, hb⟩
    · rw [site2_eq] at h
      have : (m : ℤ) = (n : ℤ) := by omega
      exact_mod_cast this
    · rw [site2_eq] at h hb
      have : (m : ℤ) = (n : ℤ) := by omega
      exact_mod_cast this
  · intro n
    change s(![(n : ℤ) + 1, (0:ℤ)], ![(n : ℤ) + 1 + 1, 0]) ∈ jkr_lineH.edgeSet
    refine (jkr_line_seg_mem ((n : ℤ) + 1)).mpr ?_
    have : (0:ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    omega


theorem jkr_lineH_not_finite : ¬ jkr_lineH.edgeSet.Finite :=
  jkr_lineH_edgeSet_infinite


theorem jkr_status :
    ¬ jwn_KeepReconnectResidue ∧
    (¬ jkr_lineH.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
      ¬ ((whb_faceRegion jkr_lineH).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1]) ∧
    jkr_lineH.edgeSet.Infinite ∧
    (jwn_KeepReconnectResidue → jkr_FiniteKeepReconnectResidue) :=
  ⟨jkr_keepReconnectResidue_false,
    ⟨jkr_pq_not_reachable, jkr_faces_not_reconnect⟩,
    jkr_lineH_edgeSet_infinite,
    jkr_finite_of_keepReconnect⟩

end Lattice
end StatMech
