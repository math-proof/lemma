/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDefectEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopTwoPointAudit
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Def.StatisticalMechanics.Code.Onsager.SignedLoopDefectEdge.Part3
open scoped BigOperators symmDiff
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ons_sourceX_eq_disorderX
    {u v : V} {Q : Finset (Sym2 V)}
    (hQsub : Q ⊆ G.edgeFinset) (hQ : HasOddBoundary Q {u, v}) (x : Real) :
    ons_sourceX G {u, v} x = ons_disorderX G Q x := by
  classical
  unfold ons_sourceX ons_disorderX
  apply Finset.sum_bij (fun F _ => F ∆ Q)
  · intro F hF
    simp only [Finset.mem_filter, Finset.mem_powerset] at hF ⊢
    refine ⟨?_, ?_⟩
    · intro e he
      rw [Finset.mem_symmDiff] at he
      exact he.elim (fun h => hF.1 h.1) (fun h => hQsub h.1)
    · rw [← hasOddBoundary_empty]
      have ht := hasOddBoundary_symmDiff hF.2 hQ
      simpa using ht
  · intro F hF H hH hEq
    calc
      F = (F ∆ Q) ∆ Q := by simp [symmDiff_assoc]
      _ = (H ∆ Q) ∆ Q := by rw [hEq]
      _ = H := by simp [symmDiff_assoc]
  · intro H hH
    simp only [Finset.mem_filter, Finset.mem_powerset] at hH
    let F := H ∆ Q
    have hFsub : F ⊆ G.edgeFinset := by
      intro e he
      rw [Finset.mem_symmDiff] at he
      exact he.elim (fun h => hH.1 h.1) (fun h => hQsub h.1)
    have hFsource : HasOddBoundary F {u, v} := by
      have hEven : HasOddBoundary H ∅ := (hasOddBoundary_empty H).2 hH.2
      have ht := hasOddBoundary_symmDiff hEven hQ
      change HasOddBoundary F (∅ ∆ {u, v}) at ht
      convert ht using 1
      ext w
      simp [Finset.mem_symmDiff]
    refine ⟨F, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hFsub, hFsource⟩
    · dsimp only [F]
      simp [symmDiff_assoc]
  · intro F hF
    simp [symmDiff_assoc]

end StatMech.Onsager
