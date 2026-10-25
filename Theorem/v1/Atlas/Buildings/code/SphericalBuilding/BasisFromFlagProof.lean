/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/BasisFromFlagProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnFlagToFrame
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.List.Pairwise


namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}


/-- A strictly monotone map $g : \mathrm{Fin}(n+1) \to \mathbb{N}$ with $g(0) = 0$ and
$g(n) = n$ must be the identity. -/
theorem strictMono_nat_id {n : ℕ}
    (g : Fin (n + 1) → ℕ) (hg : StrictMono g)
    (_h0 : g ⟨0, Nat.zero_lt_succ n⟩ = 0)
    (hn : g ⟨n, Nat.lt_succ_of_le le_rfl⟩ = n) :
    ∀ j : Fin (n + 1), g j = j.val := by
  have hlb : ∀ (j : ℕ) (hj : j < n + 1), j ≤ g ⟨j, hj⟩ := by
    intro j hj
    induction j with
    | zero => exact Nat.zero_le _
    | succ m ih =>
      have hm : m < n + 1 := by omega
      have := ih hm
      have := hg (show (⟨m, hm⟩ : Fin (n + 1)) < ⟨m + 1, hj⟩ from Fin.mk_lt_mk.mpr (by omega))
      omega
  have hub : ∀ (j : ℕ) (hj : j < n + 1), g ⟨j, hj⟩ ≤ j := by
    intro j hj
    by_contra hc
    push_neg at hc
    suffices hprop : g ⟨j, hj⟩ + (n - j) ≤ g ⟨n, by omega⟩ by omega
    have key : ∀ (k : ℕ) (hk : k < n + 1), j ≤ k →
        g ⟨j, hj⟩ + (k - j) ≤ g ⟨k, hk⟩ := by
      intro k hk hjk
      induction k with
      | zero =>
        have : j = 0 := by omega
        subst this
        simp
      | succ m ihm =>
        by_cases hjm : j ≤ m
        · have hm : m < n + 1 := by omega
          have h1 := ihm hm hjm
          have h2 := hg (show (⟨m, hm⟩ : Fin (n + 1)) < ⟨m + 1, hk⟩ from
            Fin.mk_lt_mk.mpr (by omega))
          omega
        · have : j = m + 1 := by omega
          subst this
          simp
    exact key n (by omega) (by omega)
  intro ⟨j, hj⟩
  exact Nat.le_antisymm (hub j hj) (hlb j hj)


/-- If no vector in a finite family is in the span of its predecessors (under the natural
ordering of `Fin m`), then the family is linearly independent. -/
theorem linearIndependent_of_not_mem_span_predecessors
    {V : Type*} [AddCommGroup V] [Module k V]
    {m : ℕ} (v : Fin m → V)
    (h : ∀ j : Fin m, v j ∉ Submodule.span k (v '' {i : Fin m | i.val < j.val})) :
    LinearIndependent k v := by
  induction m with
  | zero => exact linearIndependent_empty_type
  | succ p ih =>
    rw [linearIndependent_fin_succ']
    constructor
    · apply ih
      intro ⟨j, hj⟩ hmem
      apply h ⟨j, by omega⟩
      apply Submodule.span_mono _ hmem
      rintro x ⟨i, hi, hx⟩
      simp [Fin.init] at hx
      exact ⟨i.castSucc, hi, hx⟩
    · intro hmem
      apply h (Fin.last p)
      apply Submodule.span_mono _ hmem
      rintro x ⟨i, rfl⟩
      simp [Fin.init]
      exact ⟨i.castSucc, i.isLt, rfl⟩


end GLnBuilding
