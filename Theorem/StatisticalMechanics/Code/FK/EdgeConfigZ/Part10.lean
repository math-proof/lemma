/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.FK.CenteredFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Def.StatisticalMechanics.Code.FK.EdgeConfigZ.Part11
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


section BoxNesting

variable {d : ℕ}


section VanHove

variable {d : ℕ}


theorem ecz_vanHoveTag_eq_some_iff (m n : ℕ) (x : boxVerts d n) (c : Fin d → Fin (ecz_T m n)) :
    ecz_vanHoveTag m n x = some c
      ↔ ∀ i, ((x : Site d) i - ecz_center m n c i).natAbs ≤ m := by
  have hxn : ∀ i, 0 ≤ (x : Site d) i + (n : ℤ) := by
    intro i; have := (qp_natAbs_iff ((x : Site d) i) n).mp (x.2 i); linarith [this.1]
  unfold ecz_vanHoveTag
  constructor
  · intro h
    split_ifs at h with hcond
    · intro i
      have hci : (fun i => (⟨ecz_cellIdx m n (x : Site d) i, hcond i⟩ : Fin (ecz_T m n))) = c :=
        Option.some.inj h
      have hidx : ecz_cellIdx m n (x : Site d) i = (c i : ℕ) := by
        have := congrArg (fun f => (f i : ℕ)) hci; simpa using this
      
      rw [ecz_cellIdx] at hidx
      have h2m1 : 0 < 2 * m + 1 := by omega
      have hlow : (c i : ℕ) * (2 * m + 1) ≤ ((x : Site d) i + n).toNat :=
        hidx ▸ Nat.div_mul_le_self _ _
      have hhigh : ((x : Site d) i + n).toNat < ((c i : ℕ) + 1) * (2 * m + 1) := by
        rw [← hidx]
        have hdm := Nat.div_add_mod ((x : Site d) i + n).toNat (2 * m + 1)
        have hmod := Nat.mod_lt ((x : Site d) i + n).toNat h2m1
        nlinarith [hdm, hmod]
      have htoNat : (((x : Site d) i + n).toNat : ℤ) = (x : Site d) i + n :=
        Int.toNat_of_nonneg (hxn i)
      rw [qp_natAbs_iff]
      simp only [ecz_center]
      have hlowZ : ((c i : ℕ) : ℤ) * (2 * m + 1) ≤ (x : Site d) i + n := by
        have : (((c i : ℕ) * (2 * m + 1) : ℕ) : ℤ) ≤ (((x : Site d) i + n).toNat : ℤ) := by
          exact_mod_cast hlow
        rw [htoNat] at this; push_cast at this ⊢; linarith
      have hhighZ : (x : Site d) i + n < ((c i : ℕ) + 1 : ℤ) * (2 * m + 1) := by
        have : (((x : Site d) i + n).toNat : ℤ) < ((((c i : ℕ) + 1) * (2 * m + 1) : ℕ) : ℤ) := by
          exact_mod_cast hhigh
        rw [htoNat] at this; push_cast at this ⊢; linarith
      push_cast at hlowZ hhighZ ⊢
      constructor <;> nlinarith [hlowZ, hhighZ]
  · intro h
    have h2m1 : 0 < 2 * m + 1 := by omega
    
    have hidx : ∀ i, ecz_cellIdx m n (x : Site d) i = (c i : ℕ) := by
      intro i
      have hi := h i
      rw [qp_natAbs_iff] at hi
      simp only [ecz_center] at hi
      have htoNat : (((x : Site d) i + n).toNat : ℤ) = (x : Site d) i + n :=
        Int.toNat_of_nonneg (hxn i)
      
      have hlowZ : ((c i : ℤ)) * (2 * m + 1) ≤ (x : Site d) i + n := by push_cast at hi ⊢; nlinarith [hi.1]
      have hhighZ : (x : Site d) i + n < ((c i : ℤ) + 1) * (2 * m + 1) := by push_cast at hi ⊢; nlinarith [hi.2]
      rw [ecz_cellIdx]
      have hlowN : (c i : ℕ) * (2 * m + 1) ≤ ((x : Site d) i + n).toNat := by
        have : (((c i : ℕ) * (2 * m + 1) : ℕ) : ℤ) ≤ (((x : Site d) i + n).toNat : ℤ) := by
          rw [htoNat]; push_cast; linarith [hlowZ]
        exact_mod_cast this
      have hhighN : ((x : Site d) i + n).toNat < ((c i : ℕ) + 1) * (2 * m + 1) := by
        have : (((x : Site d) i + n).toNat : ℤ) < ((((c i : ℕ) + 1) * (2 * m + 1) : ℕ) : ℤ) := by
          rw [htoNat]; push_cast; linarith [hhighZ]
        exact_mod_cast this
      rw [Nat.div_eq_of_lt_le hlowN hhighN]
    have hcond : ∀ i, ecz_cellIdx m n (x : Site d) i < ecz_T m n := fun i => by
      rw [hidx i]; exact (c i).2
    rw [dif_pos hcond]
    congr 1
    funext i; apply Fin.ext; simpa using hidx i


end VanHove
end BoxNesting
end FK
end StatMech
