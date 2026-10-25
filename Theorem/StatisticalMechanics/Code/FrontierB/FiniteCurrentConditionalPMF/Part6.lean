/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditional.Part2
import Def.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part5
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

section Ambient

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem parityCurrentKernel_split
    (beta : ℝ) (H : Finset (Sym2 V)) (S : Finset G.edgeFinset)
    (a : ↑S → ℕ) (b : {e : G.edgeFinset // e ∉ S} → ℕ) :
    parityCurrentKernel G beta H ((splitEdgeCurrent G S).symm (a, b)) =
      finiteParityKernel S beta (fun e : ↑S => e.1.1 ∈ H) a *
        complementParityKernel G beta H S b := by
  unfold parityCurrentKernel finiteParityKernel complementParityKernel
  rw [← Finset.prod_filter_mul_prod_filter_not
    (Finset.univ : Finset G.edgeFinset) (fun e => e ∈ S)]
  congr 1
  · rw [Finset.prod_subtype (p := fun e => e ∈ S)
      (Finset.univ.filter (fun e => e ∈ S))
      (fun e => by simp)]
    apply Fintype.prod_congr
    intro e
    rw [splitEdgeCurrent, Equiv.piEquivPiSubtypeProd_symm_apply]
    simp [e.2]
  · rw [Finset.prod_subtype (p := fun e => e ∉ S)
      (Finset.univ.filter (fun e => e ∉ S))
      (fun e => by simp)]
    apply Fintype.prod_congr
    intro e
    rw [splitEdgeCurrent, Equiv.piEquivPiSubtypeProd_symm_apply]
    simp [e.2]

theorem tsum_ofReal_complementParityKernel
    (beta : ℝ) (hbeta : 0 < beta) (H : Finset (Sym2 V))
    (S : Finset G.edgeFinset) :
    ∑' b : {e : G.edgeFinset // e ∉ S} → ℕ,
      ENNReal.ofReal (complementParityKernel G beta H S b) = 1 := by
  exact tsum_ofReal_fintypeParityKernel beta hbeta
    (fun e : {e : G.edgeFinset // e ∉ S} => e.1.1 ∈ H)

theorem parityCurrentPMF_map_restrictCurrent
    (beta : ℝ) (hbeta : 0 < beta) (H : Finset (Sym2 V))
    (S : Finset G.edgeFinset) :
    PMF.map (restrictCurrent S) (parityCurrentPMF G beta hbeta H) =
      finiteParityPMF S beta hbeta (fun e : ↑S => e.1.1 ∈ H) := by
  apply PMF.ext
  intro a
  rw [PMF.map_apply, finiteParityPMF_apply]
  simp_rw [parityCurrentPMF_apply]
  let E := splitEdgeCurrent G S
  rw [← E.symm.tsum_eq]
  rw [ENNReal.tsum_prod']
  rw [tsum_eq_single a]
  · simp_rw [show ∀ b, restrictCurrent S (E.symm (a, b)) = a by
      intro b
      exact restrictCurrent_splitEdgeCurrent_symm G S a b]
    simp only [ite_true]
    rw [show (∑' b : {e : G.edgeFinset // e ∉ S} → ℕ,
        ENNReal.ofReal
          (parityCurrentKernel G beta H ((splitEdgeCurrent G S).symm (a, b)))) =
        ENNReal.ofReal (finiteParityKernel S beta (fun e : ↑S => e.1.1 ∈ H) a) *
          ∑' b : {e : G.edgeFinset // e ∉ S} → ℕ,
            ENNReal.ofReal (complementParityKernel G beta H S b) by
      simp_rw [parityCurrentKernel_split G beta H S a]
      have hlocal : 0 ≤
          finiteParityKernel S beta (fun e : ↑S => e.1.1 ∈ H) a :=
        Finset.prod_nonneg fun i _ =>
          parityEdgeKernel_nonneg beta hbeta (i.1.1 ∈ H) (a i)
      simp_rw [ENNReal.ofReal_mul hlocal]
      rw [ENNReal.tsum_mul_left]]
    rw [tsum_ofReal_complementParityKernel G beta hbeta H S, mul_one]
  · intro a' hne
    have hrestrict : ∀ b, restrictCurrent S (E.symm (a', b)) = a' := by
      intro b
      exact restrictCurrent_splitEdgeCurrent_symm G S a' b
    simp_rw [hrestrict]
    simp [Ne.symm hne]

end Ambient
end StatMech.FrontierB
