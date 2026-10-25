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
import Def.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part4
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option maxHeartbeats 2400000


namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsiUWeight_pos (K : Sym2 V → ℝ) (q a : ConfigSpace V) :
    0 < ghsiUWeight G K q a := by unfold ghsiUWeight; positivity

theorem ghsiTWeight_pos (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q a : ConfigSpace V) : 0 < ghsiTWeight G K hf q a := by
  unfold ghsiTWeight
  positivity

theorem ghsiFibreUU_eq_uExpectation (K : Sym2 V → ℝ) (hf : V → ℝ)
    (o x : V) (q : ConfigSpace V) :
    ghsiFibreUU G K hf o x q = ghsiUExpectation G K q
      (fun a => uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x) := by
  let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    ghsiTWeight G K hf q (ghsLTComplete q st)
  let fU : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    ghsiUWeight G K q (ghsLUComplete q su)
  let uuObs : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) o *
      uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) x
  have hM : ghsiFibreMass G K hf q = ∑ a : ConfigSpace V,
      fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsiFibreMass ghsiFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsi_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsiTWeight_split, ghsiUWeight_split]
  have hN : ghsiFibreNumerator G K hf
      (fun a b => uvar a b o * uvar a b x) q = ∑ a : ConfigSpace V,
      fT (ghsLSplitEquiv q a).1 *
        (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    unfold ghsiFibreNumerator ghsiFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    change (wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf (ghsLMate q a)) *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x) = _
    rw [ghsi_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsiTWeight_split, ghsiUWeight_split, ghsL_uvar_mul_split]
    ring
  have hZU : (∑ a : ConfigSpace V, ghsiUWeight G K q a) =
      ∑ a : ConfigSpace V, (1 : ℝ) * fU (ghsLSplitEquiv q a).2 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsiUWeight_split]
    simp [fU]
  have hNU : (∑ a : ConfigSpace V, ghsiUWeight G K q a *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x)) =
      ∑ a : ConfigSpace V, (1 : ℝ) *
        (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsiUWeight_split, ghsL_uvar_mul_split]
    ring
  have hcross := ghsL_split_cross_product (V := V) q fT (fun _ => (1 : ℝ))
    (fun su => fU su * uuObs su) fU
  unfold ghsiFibreUU ghsiFibreExpectation ghsiUExpectation
  have hm : ghsiFibreMass G K hf q ≠ 0 := (ghsiFibreMass_pos G K hf q).ne'
  have hu : (∑ a : ConfigSpace V, ghsiUWeight G K q a) ≠ 0 :=
    (Finset.sum_pos (fun a _ => ghsiUWeight_pos G K q a) Finset.univ_nonempty).ne'
  field_simp [hm, hu]
  rw [hN, hM, hZU]
  rw [show (∑ a, ghsiUWeight G K q a * uvar a (ghsLMate q a) o *
      uvar a (ghsLMate q a) x) =
      ∑ a : ConfigSpace V, (1 : ℝ) *
        (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) by
      simpa [mul_assoc] using hNU]
  simpa [mul_comm] using hcross

theorem ghsiFibreT_eq_tExpectation (K : Sym2 V → ℝ) (hf : V → ℝ)
    (y : V) (q : ConfigSpace V) :
    ghsiFibreT G K hf y q = ghsiTExpectation G K hf q
      (fun a => tvar a (ghsLMate q a) y) := by
  let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    ghsiTWeight G K hf q (ghsLTComplete q st)
  let fU : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    ghsiUWeight G K q (ghsLUComplete q su)
  let tObs : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    tvar (ghsLTComplete q st) (ghsLMate q (ghsLTComplete q st)) y
  have hM : ghsiFibreMass G K hf q = ∑ a : ConfigSpace V,
      fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsiFibreMass ghsiFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsi_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsiTWeight_split, ghsiUWeight_split]
  have hN : ghsiFibreNumerator G K hf (fun a b => tvar a b y) q =
      ∑ a : ConfigSpace V,
        (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
          fU (ghsLSplitEquiv q a).2 := by
    unfold ghsiFibreNumerator ghsiFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    change (wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf (ghsLMate q a)) *
      tvar a (ghsLMate q a) y = _
    rw [ghsi_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsiTWeight_split, ghsiUWeight_split, ghsL_tvar_split]
    ring
  have hZT : (∑ a : ConfigSpace V, ghsiTWeight G K hf q a) =
      ∑ a : ConfigSpace V, fT (ghsLSplitEquiv q a).1 * (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsiTWeight_split]
    simp [fT]
  have hNT : (∑ a : ConfigSpace V, ghsiTWeight G K hf q a *
      tvar a (ghsLMate q a) y) = ∑ a : ConfigSpace V,
      (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) * (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsiTWeight_split, ghsL_tvar_split]
    simp [fT, tObs]
  have hcross := ghsL_split_cross_product (V := V) q
    (fun st => fT st * tObs st) fT (fun _ => (1 : ℝ)) fU
  unfold ghsiFibreT ghsiFibreExpectation ghsiTExpectation
  have hm : ghsiFibreMass G K hf q ≠ 0 := (ghsiFibreMass_pos G K hf q).ne'
  have ht : (∑ a : ConfigSpace V, ghsiTWeight G K hf q a) ≠ 0 :=
    (Finset.sum_pos (fun a _ => ghsiTWeight_pos G K hf q a)
      Finset.univ_nonempty).ne'
  field_simp [hm, ht]
  rw [hN, hM, hZT, hNT]
  simpa [mul_comm] using hcross.symm


end StatMech.Ising
