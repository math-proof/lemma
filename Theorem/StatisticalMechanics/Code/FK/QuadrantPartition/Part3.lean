/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Def.StatisticalMechanics.Code.FK.QuadrantPartition.Part5
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]


section Peel

variable {T : Type*} [DecidableEq T] (tag : U → T)


theorem qp_peel_le (p q : ℝ) (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∀ S : Finset T, ∃ I : ℕ,
      qp_uu (qp_restG K₀ tag S) p q
          ≤ (∑ τ ∈ S, qp_uu (qp_blkG K₀ tag τ) p q) + (I : ℝ) * (-Real.log (1 - p))
        ∧ I ≤ ∑ τ ∈ S, (qp_straddleEdges K₀ (fun u => tag u = τ)).card := by
  intro S
  induction S using Finset.induction with
  | empty =>
    refine ⟨0, ?_, by simp⟩
    simp only [Finset.sum_empty, Nat.cast_zero, zero_mul, add_zero]
    haveI : IsEmpty {x : U // tag x ∈ (∅ : Finset T)} := ⟨fun x => by simpa using x.2⟩
    rw [qp_uu, qp_fkZ_empty, Real.log_one, neg_zero]
  | @insert τ S hτ ih =>
    obtain ⟨I0, hI0le, hI0bd⟩ := ih
    have hpart := agl_neglog_partition_le (qp_restG K₀ tag (insert τ S))
      (fun x => tag x.1 = τ) hp hp1 hq
    rw [show -Real.log (fkZ (agl_left (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q)
        = qp_uu (qp_blkG K₀ tag τ) p q from by rw [qp_uu, qp_left_eq K₀ tag τ S hτ]] at hpart
    rw [show -Real.log (fkZ (agl_right (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q)
        = qp_uu (qp_restG K₀ tag S) p q from by rw [qp_uu, qp_right_eq K₀ tag τ S hτ]] at hpart
    set Istep := agl_interfaceCard (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)
      with hIstep
    refine ⟨Istep + I0, ?_, ?_⟩
    · rw [Finset.sum_insert hτ]; push_cast
      have huu : qp_uu (qp_restG K₀ tag (insert τ S)) p q
          ≤ qp_uu (qp_blkG K₀ tag τ) p q + qp_uu (qp_restG K₀ tag S) p q
            - (Istep : ℝ) * Real.log (1 - p) := by rw [qp_uu]; exact hpart
      calc qp_uu (qp_restG K₀ tag (insert τ S)) p q
          ≤ qp_uu (qp_blkG K₀ tag τ) p q + qp_uu (qp_restG K₀ tag S) p q
              - (Istep : ℝ) * Real.log (1 - p) := huu
        _ ≤ qp_uu (qp_blkG K₀ tag τ) p q
              + ((∑ σ ∈ S, qp_uu (qp_blkG K₀ tag σ) p q) + (I0 : ℝ) * (-Real.log (1 - p)))
              - (Istep : ℝ) * Real.log (1 - p) := by linarith [hI0le]
        _ = (qp_uu (qp_blkG K₀ tag τ) p q + ∑ σ ∈ S, qp_uu (qp_blkG K₀ tag σ) p q)
              + ((Istep : ℝ) + (I0 : ℝ)) * (-Real.log (1 - p)) := by ring
    · rw [Finset.sum_insert hτ]
      have hIstepbd : Istep ≤ (qp_straddleEdges K₀ (fun u => tag u = τ)).card :=
        le_trans (qp_interface_le_straddle (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ))
          (qp_restG_straddle_le K₀ tag τ S)
      omega

end Peel
end FK
end StatMech
