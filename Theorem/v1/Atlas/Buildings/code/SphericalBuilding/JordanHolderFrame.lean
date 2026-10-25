/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderFrame.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.JordanHolderPermutation.Part3
import Lemma.Fin.LeFinrank.of.Le.GtVal_0
import Lemma.Fin.GapVector.in.Spaces.of.LtVal_Val.IsStrictFlag
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.RefinementCompatibility
import Def.v1.Atlas.Buildings.code.SphericalBuilding.JordanHolderFrame
set_option maxHeartbeats 800000


namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- The Jordan-Hölder line vector $\ell_i$ lies in $V_{i+1}$ of the flag $\sigma$. -/
theorem jhLine_mem_Vi_succ (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) (i : Fin n) :
    jhLine σ τ hσ hτ i ∈ σ.spaces ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ :=
  jhGapVector_mem_Vi σ τ hσ hτ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)

/-- The Jordan-Hölder line vector $\ell_i$ does **not** lie in $V_i$, i.e., it realizes a
genuine dimension jump. -/
theorem jhLine_not_mem_Vi (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) (i : Fin n) :
    jhLine σ τ hσ hτ i ∉ σ.spaces ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
  have h := jhGapVector_not_mem_lower σ τ hσ hτ
    ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)

  simp only [Nat.succ_sub_one] at h
  exact h

/-- Each Jordan-Hölder line vector is nonzero. -/
theorem jhLine_ne_zero (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) (i : Fin n) :
    jhLine σ τ hσ hτ i ≠ 0 :=
  jhGapVector_ne_zero σ τ hσ hτ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)

/-- Monotonicity: if $i + 1 \le j$ then $\ell_i \in V_j$. -/
theorem jhLine_mem_of_le (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin n) (j : Fin (n + 1)) (hij : i.val + 1 ≤ j.val) :
    jhLine σ τ hσ hτ i ∈ σ.spaces j :=
  σ.monotone (Fin.mk_le_mk.mpr hij) (jhLine_mem_Vi_succ σ τ hσ hτ i)

/-- The Jordan-Hölder line vectors $\{\ell_i\}_{i < n}$ are linearly independent in $k^n$. -/
theorem jhLine_linearIndependent (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) :
    LinearIndependent k (fun i : Fin n => jhLine σ τ hσ hτ i) := by
  suffices ∀ (m : ℕ) (hm : m ≤ n),
      LinearIndependent k (fun i : Fin m => jhLine σ τ hσ hτ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) by
    have h := this n le_rfl
    convert h using 1
  intro m
  induction m with
  | zero => intro _; exact linearIndependent_empty_type
  | succ p ih =>
    intro hp
    rw [linearIndependent_fin_succ']
    constructor
    · convert ih (by omega) using 1
    · intro hmem
      have hspan_le : Submodule.span k (Set.range (Fin.init (fun i : Fin (p + 1) =>
          jhLine σ τ hσ hτ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hp⟩))) ≤ σ.spaces ⟨p, Nat.lt_succ_of_lt (by omega)⟩ := by
        rw [Submodule.span_le]
        rintro x ⟨⟨j, hj⟩, rfl⟩
        simp only [Fin.init]
        exact jhLine_mem_of_le σ τ hσ hτ ⟨j, by omega⟩ ⟨p, by omega⟩ (by simp; omega)
      exact jhLine_not_mem_Vi σ τ hσ hτ ⟨p, by omega⟩ (hspan_le hmem)

/-- The span of the $n$ Jordan-Hölder line vectors equals all of $k^n$. -/
theorem jhLine_span_eq_top (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) [FiniteDimensional k (Vec k n)] :
    Submodule.span k (Set.range (fun i : Fin n => jhLine σ τ hσ hτ i)) = ⊤ := by
  apply (jhLine_linearIndependent σ τ hσ hτ).span_eq_top_of_card_eq_finrank'
  simp

end GLnBuilding
