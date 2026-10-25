/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalRatio.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterAgreementComplementRatio
import Mathlib.Combinatorics.SetFamily.FourFunctions
open Finset


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem ghsiSubsetMass_mul_compl_le_interCompl_mul_union
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    (A B : Finset V) :
    ghsiSubsetMass G K hf A * ghsiSubsetMass G K hf Bᶜ <=
      ghsiSubsetMass G K hf (A ∩ B)ᶜ *
        ghsiSubsetMass G K hf (A ∪ B) := by
  have hratio := ghsiSubsetMass_compl_ratio_mono G K hf hK hhf
    (show Bᶜ ⊆ (A ∩ B)ᶜ by
      intro x hx
      simp only [mem_compl, mem_inter] at hx ⊢
      exact fun h => hx h.2)
  have hlog := ghsiSubsetMass_logSupermodular G K hf hK hhf A B
  have hB : 0 < ghsiSubsetMass G K hf B := by
    unfold ghsiSubsetMass
    exact mul_pos (ZJ_pos _ _ _) (ZJ_pos _ _ _)
  have hI : 0 < ghsiSubsetMass G K hf (A ∩ B) := by
    unfold ghsiSubsetMass
    exact mul_pos (ZJ_pos _ _ _) (ZJ_pos _ _ _)
  simp only [compl_compl] at hratio
  have hprod := mul_le_mul hlog hratio
    (mul_nonneg (ghsiSubsetMass_nonneg G K hf Bᶜ)
      (ghsiSubsetMass_nonneg G K hf (A ∩ B)))
    (mul_nonneg (ghsiSubsetMass_nonneg G K hf (A ∪ B))
      (ghsiSubsetMass_nonneg G K hf (A ∩ B)))
  nlinarith [hprod, mul_pos hB hI]


end
end StatMech.Ising
