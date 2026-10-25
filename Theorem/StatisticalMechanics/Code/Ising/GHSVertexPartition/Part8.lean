/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Walls.ghysupermult.Part2
import Def.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part7
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls

variable {W : Type*} [Fintype W] [DecidableEq W]


variable {V : Type*} [Fintype V] [DecidableEq V]


theorem ghsvp_disagreementCorr_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : Real) (hβ : 0 <= β) (o x : V) (A : Finset V) :
    0 <= ghsvp_disagreementCorr G β o x A := by
  unfold ghsvp_disagreementCorr
  split_ifs
  · exact le_rfl
  · apply ghsvp_vertexCorr_nonneg
    intro e
    positivity


theorem ghsvp_disagreementCorr_antitone (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : Real) (hβ : 0 <= β) (o x : V) :
    Antitone (ghsvp_disagreementCorr G β o x) := by
  intro A B hAB
  by_cases hA : o ∈ A ∨ x ∈ A
  · have hB : o ∈ B ∨ x ∈ B := hA.elim (fun ho => Or.inl (hAB ho))
      (fun hx => Or.inr (hAB hx))
    simp [ghsvp_disagreementCorr, hA, hB]
  · by_cases hB : o ∈ B ∨ x ∈ B
    · simp only [ghsvp_disagreementCorr, if_pos hB, if_neg hA]
      apply ghsvp_vertexCorr_nonneg
      intro e
      positivity
    · simp only [ghsvp_disagreementCorr, if_neg hA, if_neg hB]
      apply ghsvp_vertexCorr_mono
      · intro e
        positivity
      · exact fun e he => SimpleGraph.not_isDiag_of_mem_edgeFinset he
      · intro v hv
        simp only [Finset.mem_compl] at hv ⊢
        exact fun hvA => hv (hAB hvA)

theorem ghsvp_agreementMag_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (hβ : 0 <= β) (hh : 0 <= h) (y : V) (A : Finset V) :
    0 <= ghsvp_agreementMag G β h y A := by
  unfold ghsvp_agreementMag
  split_ifs
  · apply ghsvp_vertexCorrField_nonneg
    · intro e
      positivity
    · intro v
      positivity
  · exact le_rfl


theorem ghsvp_agreementMag_monotone (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (hβ : 0 <= β) (hh : 0 <= h) (y : V) :
    Monotone (ghsvp_agreementMag G β h y) := by
  intro A B hAB
  by_cases hB : y ∈ B
  · by_cases hA : y ∈ A
    · simp only [ghsvp_agreementMag, if_pos hA, if_pos hB]
      apply ghsvp_vertexCorrField_mono
      · intro e
        positivity
      · intro v
        positivity
      · exact fun e he => SimpleGraph.not_isDiag_of_mem_edgeFinset he
      · exact hAB
    · simp only [ghsvp_agreementMag, if_neg hA, if_pos hB]
      apply ghsvp_vertexCorrField_nonneg
      · intro e
        positivity
      · intro v
        positivity
  · have hA : y ∉ A := fun hy => hB (hAB hy)
    simp [ghsvp_agreementMag, hA, hB]

end StatMech.Ising
