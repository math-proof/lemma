/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditional.Part2
import Def.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part3
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem finiteParityPMF_apply {E : Type*} [DecidableEq E]
    (S : Finset E) (beta : ℝ) (hbeta : 0 < beta)
    (odd : ↑S → Bool) (a : ↑S → ℕ) :
    finiteParityPMF S beta hbeta odd a =
      ENNReal.ofReal (finiteParityKernel S beta odd a) := by
  rw [finiteParityPMF, PMF.normalize_apply,
    tsum_ofReal_finiteParityKernel S beta hbeta odd]
  simp

theorem tsum_ofReal_fintypeParityKernel
    {I : Type*} [Fintype I] [DecidableEq I]
    (beta : ℝ) (hbeta : 0 < beta) (odd : I → Bool) :
    ∑' a : I → ℕ,
      ENNReal.ofReal (∏ i, parityEdgeKernel beta (odd i) (a i)) = 1 := by
  let U : Finset I := Finset.univ
  let e : ↑U ≃ I := Equiv.ofBijective Subtype.val ⟨fun _ _ h => Subtype.ext h,
    fun i => ⟨⟨i, Finset.mem_univ i⟩, rfl⟩⟩
  let E : (↑U → ℕ) ≃ (I → ℕ) :=
    Equiv.arrowCongr e (Equiv.refl ℕ)
  rw [← E.tsum_eq]
  have hnorm := tsum_ofReal_finiteParityKernel U beta hbeta
    (fun i : ↑U => odd i.1)
  rw [← hnorm]
  apply tsum_congr
  intro a
  congr 1
  unfold finiteParityKernel
  symm
  apply Fintype.prod_equiv e
  intro i
  simp [E, e, U]

end StatMech.FrontierB
