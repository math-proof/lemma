/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part5
import Def.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF.Part3
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising


theorem nonnegativeFiniteParityPMF_apply
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) (odd : ↑S → Bool)
    (a : ↑S → ℕ) :
    nonnegativeFiniteParityPMF S lambda hlambda odd a =
      ENNReal.ofReal (nonnegativeFiniteParityKernel S lambda odd a) := by
  rw [nonnegativeFiniteParityPMF, PMF.normalize_apply,
    tsum_ofReal_nonnegativeFiniteParityKernel S lambda hlambda odd]
  simp

theorem nonnegativeFiniteParityPMF_eq_zero_of_ne
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) (odd : ↑S → Bool)
    (a : ↑S → Nat) (hodd : odd ≠ currentLocalParity a) :
    nonnegativeFiniteParityPMF S lambda hlambda odd a = 0 := by
  rw [nonnegativeFiniteParityPMF_apply]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hodd
  apply ENNReal.ofReal_eq_zero.mpr
  apply le_of_eq
  unfold nonnegativeFiniteParityKernel
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply nonnegativeParityEdgeKernel_eq_zero_of_parity_ne
  cases h : odd i <;> simp [h, currentLocalParity] at hi ⊢ <;> assumption

theorem bind_nonnegativeFiniteParityPMF_apply
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1)
    (p : PMF (↑S → Bool)) (a : ↑S → Nat) :
    p.bind (nonnegativeFiniteParityPMF S lambda hlambda) a =
      p (currentLocalParity a) *
        nonnegativeFiniteParityPMF S lambda hlambda
          (currentLocalParity a) a := by
  rw [PMF.bind_apply, tsum_eq_single (currentLocalParity a)]
  intro odd hodd
  rw [nonnegativeFiniteParityPMF_eq_zero_of_ne
    S lambda hlambda odd a hodd]
  simp

section Graph

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem inhomogeneousParityFiberMass_nonneg
    (lambda : Sym2 V → ℝ)
    (hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1)
    (H : Finset (Sym2 V)) :
    0 ≤ inhomogeneousParityFiberMass G lambda H := by
  unfold inhomogeneousParityFiberMass
  exact Finset.prod_nonneg fun e _ => by
    by_cases he : e.1 ∈ H
    · simp only [if_pos he]
      exact Real.sinh_nonneg_iff.mpr (hlambda e)
    · simp only [if_neg he]
      exact (Real.cosh_pos _).le


end Graph
end StatMech.FrontierB
