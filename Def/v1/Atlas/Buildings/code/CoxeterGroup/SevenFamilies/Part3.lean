/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SevenFamilies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeACoxeterSystem.Part2
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper
import Def.v1.Atlas.Buildings.code.CoxeterGroup.SignedPermGroup.Part2
import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeCInjectivityHelper
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.SevenFamilies.Part2


namespace CoxeterMatrix

/-- The affine type-$\tilde B_n$ Coxeter matrix. -/
def typeAffinB (n : ℕ) : CoxeterMatrix (Fin (n + 1)) where
  M := Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 1
    else if affinBCond i.val j.val then
      if max i.val j.val = n then 4 else 3
    else 2
  isSymm := by
    ext i j; simp only [Matrix.of_apply, Matrix.transpose_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : ¬(j = i) := fun h => hij h.symm
      simp only [hij, hji, ite_false]
      simp only [affinBCond_comm, max_comm]
  diagonal := by intro i; simp [Matrix.of_apply]
  off_diagonal := by
    intro i j hij; simp only [Matrix.of_apply, hij, ite_false]
    split_ifs <;> omega

/-- The affine type-$\tilde C_n$ Coxeter matrix. -/
def typeAffinC (n : ℕ) : CoxeterMatrix (Fin (n + 1)) where
  M := Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 1
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then
      if min i.val j.val = 0 ∨ max i.val j.val = n then 4
      else 3
    else 2
  isSymm := by
    ext i j; simp only [Matrix.of_apply, Matrix.transpose_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : ¬(j = i) := fun h => hij h.symm
      simp only [hij, hji, ite_false]
      have adj_symm : (i.val + 1 = j.val ∨ j.val + 1 = i.val) ↔
                       (j.val + 1 = i.val ∨ i.val + 1 = j.val) :=
        ⟨fun h => h.symm, fun h => h.symm⟩
      have minmax_symm : (min i.val j.val = 0 ∨ max i.val j.val = n) ↔
                          (min j.val i.val = 0 ∨ max j.val i.val = n) := by
        rw [min_comm, max_comm]
      split_ifs with h1 h2 h3 h4 h5 h6
      all_goals first | rfl | (exfalso; simp_all)
  diagonal := by intro i; simp [Matrix.of_apply]
  off_diagonal := by
    intro i j hij; simp only [Matrix.of_apply, hij, ite_false]
    split_ifs <;> omega

/-- The affine type-$\tilde D_n$ Coxeter matrix. -/
def typeAffinD (n : ℕ) : CoxeterMatrix (Fin (n + 1)) where
  M := Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 1
    else if affinDCond n i.val j.val then 3
    else 2
  isSymm := by
    ext i j; simp only [Matrix.of_apply, Matrix.transpose_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : ¬(j = i) := fun h => hij h.symm
      simp only [hij, hji, ite_false]
      simp only [affinDCond_comm]
  diagonal := by intro i; simp [Matrix.of_apply]
  off_diagonal := by
    intro i j hij; simp only [Matrix.of_apply, hij, ite_false]
    split_ifs <;> omega

end CoxeterMatrix
