/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAIsomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.PresentedGroup
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper
import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeAIsomorphism.Part2
open Equiv Equiv.Perm Function Set


namespace SymmetricCoxeter

/-- `coxeterToPermHom` sends the $i$-th simple generator to the $i$-th adjacent transposition. -/
theorem coxeterToPermHom_generator (n : ℕ) (i : Fin n) :
    coxeterToPermHom n (CoxeterMatrix.simple (CoxeterMatrix.A n) i) = adjTransposition n i :=
  PresentedGroup.toGroup.of _

/-- `coxeterToPermHom` is surjective: adjacent transpositions generate $S_{n+1}$. -/
theorem coxeterToPermHom_surjective (n : ℕ) :
    Function.Surjective (coxeterToPermHom n) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  have hgen : ∀ i : Fin n, adjTransposition n i ∈ (coxeterToPermHom n).range :=
    fun i => ⟨_, coxeterToPermHom_generator n i⟩
  intro σ _
  have hmcl := Equiv.Perm.mclosure_swap_castSucc_succ n
  have hσ : σ ∈ Submonoid.closure
      (Set.range fun i : Fin n => Equiv.swap (Fin.castSucc i) (Fin.succ i)) := by
    rw [hmcl]; exact Submonoid.mem_top σ
  have hle : Submonoid.closure
      (Set.range fun i : Fin n => Equiv.swap (Fin.castSucc i) (Fin.succ i)) ≤
      (coxeterToPermHom n).range.toSubmonoid := by
    exact Submonoid.closure_le.mpr (fun x ⟨i, hi⟩ => hi ▸ hgen i)
  exact hle hσ

/-- `coxeterToPermHom` is injective, completing the isomorphism $W(A_{n-1}) \cong S_{n+1}$. -/
theorem coxeterToPermHom_injective (n : ℕ) :
    Function.Injective (coxeterToPermHom n) :=
  typeA_coxeterGroup_toPermHom_injective n (adjTransposition_lift_rels n)

end SymmetricCoxeter
