/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
import Theorem.StatisticalMechanics.Code.Sharpness.GHSConcavity
import Def.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part3
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option maxHeartbeats 2400000


namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsiFibreWeight_pos (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q a : ConfigSpace V) : 0 < ghsiFibreWeight G K hf q a :=
  mul_pos (wJ_pos _ _ _ _) (wJ_pos _ _ _ _)

theorem ghsiFibreMass_pos (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q : ConfigSpace V) : 0 < ghsiFibreMass G K hf q := by
  unfold ghsiFibreMass
  exact Finset.sum_pos (fun a _ => ghsiFibreWeight_pos G K hf q a)
    Finset.univ_nonempty

theorem ghsiAgreementProb_nonneg (K : Sym2 V → ℝ) (hf : V → ℝ) :
    0 ≤ ghsiAgreementProb G K hf := fun q =>
  div_nonneg (ghsiFibreMass_pos G K hf q).le (sq_nonneg _)

theorem ghsiAgreementProb_sum_eq_one (K : Sym2 V → ℝ) (hf : V → ℝ) :
    ∑ q : ConfigSpace V, ghsiAgreementProb G K hf q = 1 := by
  have hreindex := ghsL_sum_pair_xnor (V := V)
    (fun a b => wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf b)
  have hmass : (∑ q : ConfigSpace V, ghsiFibreMass G K hf q) =
      (ZJ G.edgeFinset K hf) ^ 2 := by
    unfold ghsiFibreMass ghsiFibreWeight ZJ
    rw [← hreindex, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  unfold ghsiAgreementProb
  rw [← Finset.sum_div, hmass]
  exact div_self (pow_ne_zero 2 (ZJ_pos _ _ _).ne')


theorem ghsiAgreementProb_fkg (K : Sym2 V → ℝ) (hf : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x) :
    FKGLatticeCondition (ghsiAgreementProb G K hf) := by
  intro q r
  have hsub := ghsiSubsetMass_logSupermodular G K hf hK hhf
    (ghsLAgreeFinset q) (ghsLAgreeFinset r)
  rw [← ghsLAgreeFinset_sup, ← ghsLAgreeFinset_inf] at hsub
  have hscale : ∀ q : ConfigSpace V,
      ghsiSubsetMass G K hf (ghsLAgreeFinset q) =
        (4 * Fintype.card (ConfigSpace V)) * ghsiFibreMass G K hf q := by
    intro q
    let T := (v : {v : V // q v = true}) → Bool
    let U := (v : {v : V // ¬ q v = true}) → Bool
    let fT : T → ℝ := fun st => ghsiTWeight G K hf q (ghsLTComplete q st)
    let fU : U → ℝ := fun su => ghsiUWeight G K q (ghsLUComplete q su)
    have hmass : ghsiFibreMass G K hf q =
        (∑ st : T, fT st) * ∑ su : U, fU su := by
      unfold ghsiFibreMass ghsiFibreWeight
      calc
        (∑ a : ConfigSpace V,
            wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf (ghsLMate q a)) =
            ∑ a : ConfigSpace V,
              fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [ghsi_duplicateWeight_eq_tWeight_mul_uWeight,
            ghsiTWeight_split, ghsiUWeight_split]
        _ = _ := ghsL_split_sum_product q fT fU
    have ht : ghsiTZ G K hf (ghsLAgreeFinset q) =
        (∑ st : T, fT st) * Fintype.card U := by
      unfold ghsiTZ ZJ
      have hs := ghsL_split_sum_product (V := V) q fT (fun _ : U => (1 : ℝ))
      rw [show (∑ a : ConfigSpace V,
          wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
            (fun e => 2 * K e)
            (fun x => if x ∈ ghsLAgreeFinset q then 2 * hf x else 0) a) =
          ∑ a : ConfigSpace V, fT (ghsLSplitEquiv q a).1 * (1 : ℝ) by
        apply Finset.sum_congr rfl
        intro a _
        rw [← ghsiTWeight_eq_wJ_restricted,
          ghsiTWeight_split]
        simp [fT]]
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hs
    have hu : ghsiUZ G K (ghsLAgreeFinset q)ᶜ =
        Fintype.card T * ∑ su : U, fU su := by
      unfold ghsiUZ ZJ
      have hs := ghsL_split_sum_product (V := V) q (fun _ : T => (1 : ℝ)) fU
      rw [show (∑ a : ConfigSpace V,
          wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ)
            (fun e => 2 * K e) (fun _ => 0) a) =
          ∑ a : ConfigSpace V, (1 : ℝ) * fU (ghsLSplitEquiv q a).2 by
        apply Finset.sum_congr rfl
        intro a _
        rw [← ghsiUWeight_eq_wJ,
          ghsiUWeight_split]
        simp [fU]]
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hs
    have hcard : Fintype.card (ConfigSpace V) = Fintype.card T * Fintype.card U := by
      rw [Fintype.card_congr (ghsLSplitEquiv q), Fintype.card_prod]
    rw [ghsiSubsetMass_eq_four_mul_tZ_uZ, ht, hu, hmass, hcard]
    norm_num [Nat.cast_mul]
    ring
  simp_rw [hscale] at hsub
  have hc : 0 < (4 * Fintype.card (ConfigSpace V) : ℝ) := by
    have := Fintype.card_pos_iff.mpr (show Nonempty (ConfigSpace V) from ⟨fun _ => false⟩)
    positivity
  have hfibre : ghsiFibreMass G K hf q * ghsiFibreMass G K hf r ≤
      ghsiFibreMass G K hf (q ⊔ r) * ghsiFibreMass G K hf (q ⊓ r) := by
    nlinarith [hsub, sq_pos_of_pos hc]
  unfold ghsiAgreementProb
  rw [div_mul_div_comm, div_mul_div_comm]
  exact div_le_div_of_nonneg_right hfibre (mul_nonneg (sq_nonneg _) (sq_nonneg _))


end StatMech.Ising
