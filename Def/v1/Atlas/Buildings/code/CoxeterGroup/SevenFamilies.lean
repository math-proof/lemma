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
import Abbrev.v1.Atlas.Buildings.code.CoxeterGroup.SevenFamilies


namespace CoxeterMatrix

/-- The affine type-$\tilde A_n$ Coxeter matrix: linear diagram on $n+1$ nodes wrapped into a cycle. -/
def typeAffinA (n : ℕ) : CoxeterMatrix (Fin (n + 1)) where
  M := Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 1
    else if (i.val + 1) % (n + 1) = j.val ∨ (j.val + 1) % (n + 1) = i.val then
      if n ≤ 1 then 0
      else 3
    else 2
  isSymm := by
    ext i j; simp only [Matrix.of_apply, Matrix.transpose_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : ¬(j = i) := fun h => hij h.symm
      simp only [hij, hji, ite_false]
      congr 1
      exact propext ⟨fun h => h.symm, fun h => h.symm⟩
  diagonal := by intro i; simp [Matrix.of_apply]
  off_diagonal := by
    intro i j hij; simp only [Matrix.of_apply, hij, ite_false]
    split_ifs <;> omega

/-- The Coxeter group of type $A_{n-1}$ is the symmetric group $S_n = \operatorname{Perm}(\operatorname{Fin}(n+1))$. -/
noncomputable def equiv_perm_mulEquiv_coxeterGroup_typeA (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) ≃* (typeA n).Group :=
  SymGroupCoxeter.symGroup_mulEquiv n

/-- The canonical Coxeter system structure on $S_n$ for type $A_{n-1}$. -/
noncomputable def typeA_coxeterSystem (n : ℕ) :
    CoxeterSystem (typeA n) (Equiv.Perm (Fin (n + 1))) :=
  SymGroupCoxeter.symGroup_coxeterSystem n

/-- The Coxeter group of type $C_n$ is the signed permutation group $S_n^\pm = (\{\pm 1\})^n \rtimes S_n$. -/
noncomputable def typeC_signedPermGroup_mulEquiv (n : ℕ) :
    SignedPerm.SignedPermGroup n ≃* (typeC n).Group :=
  typeC_signedPerm_mulEquiv n

/-- The canonical Coxeter system structure on the signed permutation group for type $C_n$. -/
noncomputable def typeC_coxeterSystem (n : ℕ) :
    CoxeterSystem (typeC n) (SignedPerm.SignedPermGroup n) :=
  ⟨typeC_signedPermGroup_mulEquiv n⟩

end CoxeterMatrix

/-- Adjacency predicate encoding the edges of the affine type-$\tilde B_n$ Dynkin diagram. -/
def affinBCond (i j : ℕ) : Prop :=
  (i = 0 ∧ j = 2) ∨ (j = 0 ∧ i = 2) ∨
  (i = 1 ∧ j = 2) ∨ (j = 1 ∧ i = 2) ∨
  (i + 1 = j ∧ i ≥ 2) ∨ (j + 1 = i ∧ j ≥ 2)

