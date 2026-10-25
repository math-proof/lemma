/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem centered_offset_natAbs_le (n : Nat) (k : Fin (2 * n)) :
    ((k.val : Int) - (n : Int)).natAbs ≤ n := by
  have hk : k.val < 2 * n := k.isLt
  have hlo : -(n : Int) ≤ (k.val : Int) - (n : Int) := by omega
  have hhi : (k.val : Int) - (n : Int) ≤ (n : Int) := by omega
  have habs : |(k.val : Int) - (n : Int)| ≤ (n : Int) :=
    abs_le.mpr ⟨hlo, hhi⟩
  rw [Int.abs_eq_natAbs] at habs
  exact_mod_cast habs

theorem centered_reverse_natAbs_le (n : Nat) (k : Fin (2 * n)) :
    ((n : Int) - (k.val : Int)).natAbs ≤ n := by
  rw [show (n : Int) - (k.val : Int) = -((k.val : Int) - n) by ring,
    Int.natAbs_neg]
  exact centered_offset_natAbs_le n k


end
end StatMech.Universality
