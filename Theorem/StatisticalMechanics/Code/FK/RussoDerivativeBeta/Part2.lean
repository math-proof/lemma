/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.RussoDerivativeBeta.Part2
open scoped BigOperators


namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


lemma edgeProductWOff_update (pf : Sym2 V → ℝ) (e₀ : Sym2 V) (t : ℝ)
    (ω : ConfigSpace (Sym2 V)) :
    edgeProductWOff G (Function.update pf e₀ t) e₀ ω = edgeProductWOff G pf e₀ ω := by
  unfold edgeProductWOff
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have hne : j ≠ e₀ := (Finset.mem_erase.1 hj).1
  rw [Function.update_of_ne hne]


lemma edgeProductW_update_factor (pf : Sym2 V → ℝ) (e₀ : Sym2 V) (t : ℝ)
    (ω : ConfigSpace (Sym2 V)) (he : e₀ ∈ G.edgeFinset) :
    edgeProductW G (Function.update pf e₀ t) ω
      = edgeProductWOff G pf e₀ ω * (if ω e₀ then t else 1 - t) := by
  unfold edgeProductW
  rw [← Finset.prod_erase_mul G.edgeFinset _ he]
  congr 1
  · rw [← edgeProductWOff_update G pf e₀ t ω]; rfl
  · rw [Function.update_self]


lemma hasDerivAt_edgeProductW_update (pf : Sym2 V → ℝ) (e₀ : Sym2 V) (t : ℝ)
    (ω : ConfigSpace (Sym2 V)) (he : e₀ ∈ G.edgeFinset) :
    HasDerivAt (fun t => edgeProductW G (Function.update pf e₀ t) ω)
      (edgeProductWOff G pf e₀ ω * (if ω e₀ then (1 : ℝ) else -1)) t := by
  have hfac : (fun t => edgeProductW G (Function.update pf e₀ t) ω)
      = (fun t => edgeProductWOff G pf e₀ ω * (if ω e₀ then t else 1 - t)) := by
    funext s; exact edgeProductW_update_factor G pf e₀ s ω he
  rw [hfac]
  have hfactor : HasDerivAt (fun t => if ω e₀ then t else 1 - t)
      (if ω e₀ then (1 : ℝ) else -1) t := by
    by_cases h : ω e₀
    · simp only [h, if_true]; exact hasDerivAt_id t
    · simp only [h]
      convert (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t) using 1
      · ext s
        simp [id]
      · simp
  exact hfactor.const_mul (edgeProductWOff G pf e₀ ω)


lemma hasDerivAt_edgeProductW_clean {pf : Sym2 V → ℝ} {e₀ : Sym2 V} {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (ω : ConfigSpace (Sym2 V)) (he : e₀ ∈ G.edgeFinset) :
    HasDerivAt (fun t => edgeProductW G (Function.update pf e₀ t) ω)
      (edgeProductW G (Function.update pf e₀ t) ω
        * ((coordR e₀ ω - t) / (t * (1 - t)))) t := by
  refine (hasDerivAt_edgeProductW_update G pf e₀ t ω he).congr_deriv ?_
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  have htne : t ≠ 0 := ht.ne'
  have ht1ne : (1 : ℝ) - t ≠ 0 := ht1'.ne'
  rw [edgeProductW_update_factor G pf e₀ t ω he]
  unfold coordR
  by_cases h : ω e₀ = true
  · rw [if_pos h, if_pos h, if_pos h]; field_simp
  · rw [if_neg h, if_neg h, if_neg h]; field_simp; ring


lemma hasDerivAt_fkWeightW {pf : Sym2 V → ℝ} {e₀ : Sym2 V} {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (q : ℝ) (ω : ConfigSpace (Sym2 V))
    (he : e₀ ∈ G.edgeFinset) :
    HasDerivAt (fun t => fkWeightW G (Function.update pf e₀ t) q ω)
      (fkWeightW G (Function.update pf e₀ t) q ω
        * ((coordR e₀ ω - t) / (t * (1 - t)))) t := by
  have h := (hasDerivAt_edgeProductW_clean (pf := pf) G ht ht1 ω he).mul_const
    (q ^ numClusters G ω)
  refine h.congr_deriv ?_
  unfold fkWeightW
  ring


end FK
end StatMech
