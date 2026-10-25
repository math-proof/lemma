/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterDisentangling
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFourCurrent
import Theorem.StatisticalMechanics.Code.Ising.FreeCorrelationDomainMonotonicity
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterConfinement.Part3
open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem finiteTreeClusterConfinementMass_eq_fibers
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (k l : V) (S : Finset V) :
    finiteTreeClusterConfinementMass G beta J k l S =
      ∑ T : Finset V, if k ∈ T then
        finiteTreeSafeRegionFiber G beta J Sᶜ T {k, l} ∅ else 0 := by
  let P : Current V -> Prop := fun n => k ∈ finiteTreeSafeRegion G n Sᶜ
  let f : Current V -> Finset V := fun n => finiteTreeSafeRegion G n Sᶜ
  have hpart := gatedSourcePairSum_partition G beta J {k, l} ∅ P f
  unfold finiteTreeClusterConfinementMass
  change gatedSourcePairSum G beta J {k, l} ∅ P = _
  rw [hpart]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hkT : k ∈ T
  · rw [if_pos hkT]
    unfold finiteTreeSafeRegionFiber
    apply gatedSourcePairSum_congr_sources
    intro p q hp hq
    dsimp only [P, f]
    constructor
    · exact And.left
    · intro hT
      exact ⟨hT, by simpa [hT] using hkT⟩
  · rw [if_neg hkT]
    rw [gatedSourcePairSum_congr_sources G beta J {k, l} ∅
      (fun n => f n = T ∧ P n) (fun _ => False)]
    · unfold gatedSourcePairSum
      simp
    · intro p q hp hq
      constructor
      · rintro ⟨hT, hkSafe⟩
        apply (hkT ?_).elim
        rw [← hT]
        exact hkSafe
      · exact False.elim

theorem sum_finiteTreeSafeRegionFiber_vacuum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (roots : Finset V) :
    ∑ T : Finset V, finiteTreeSafeRegionFiber G beta J roots T ∅ ∅ =
      currentSum G beta J ∅ ^ 2 := by
  let f : Current V -> Finset V := fun n => finiteTreeSafeRegion G n roots
  have hpart := gatedSourcePairSum_partition G beta J ∅ ∅
    (fun _ => True) f
  calc
    (∑ T : Finset V, finiteTreeSafeRegionFiber G beta J roots T ∅ ∅) =
        ∑ T : Finset V, gatedSourcePairSum G beta J ∅ ∅
          (fun n => f n = T ∧ True) := by
      apply Finset.sum_congr rfl
      intro T _
      unfold finiteTreeSafeRegionFiber
      apply gatedSourcePairSum_congr_sources
      intro p q hp hq
      simp only [and_true, f]
    _ = gatedSourcePairSum G beta J ∅ ∅ (fun _ => True) := hpart.symm
    _ = sourcePairSum G beta J ∅ ∅ := gatedSourcePairSum_true G beta J ∅ ∅
    _ = currentSum G beta J ∅ ^ 2 := by
      rw [sourcePairSum_eq_mul]
      ring


theorem finiteTreeClusterConfinementMass_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {k l : V} (hkl : k ≠ l) (S : Finset V) :
    finiteTreeClusterConfinementMass G beta J k l S <=
      expectationJ G beta (couplingIn J S) {k, l} *
        currentSum G beta J ∅ ^ 2 := by
  rw [finiteTreeClusterConfinementMass_eq_fibers]
  rw [← sum_finiteTreeSafeRegionFiber_vacuum G beta J Sᶜ,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T hT
  have hvac := finiteTreeSafeRegionFiber_nonneg
    G beta J hbeta hJ Sᶜ T ∅ ∅
  have hcorrS : 0 <= expectationJ G beta (couplingIn J S) {k, l} :=
    StatMech.Ising.acr_expectationJ_nonneg G beta (couplingIn J S) hbeta
      (fun e => by
        unfold couplingIn
        split <;> simp_all [hJ e]) {k, l}
  by_cases hkT : k ∈ T
  · rw [if_pos hkT]
    by_cases hTS : T ⊆ S
    · by_cases hlT : l ∈ T
      · rw [finiteTreeSafeRegionFiber_sourceReplacement G beta J Sᶜ T
          {k, l} (by
            intro v hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl
            · exact hkT
            · exact hlT)]
        apply mul_le_mul_of_nonneg_right
        · exact expectationJ_couplingIn_mono_domain G beta J hbeta hJ
            hTS {k, l}
        · exact hvac
      · have hzero : finiteTreeSafeRegionFiber G beta J Sᶜ T {k, l} ∅ = 0 := by
          unfold finiteTreeSafeRegionFiber
          rw [gatedSourcePairSum_congr_sources G beta J {k, l} ∅
            (fun n => finiteTreeSafeRegion G n Sᶜ = T) (fun _ => False)]
          · unfold gatedSourcePairSum
            simp
          · intro p q hp hq
            constructor
            · intro heq
              have hconnP := currentConnected_of_sources_pair G p hkl hp
              have hconn := grahamCurrentConnected_add_right G p q hconnP
              have hkSafe : k ∈ finiteTreeSafeRegion G
                  (ofEdgeFun G (fun e => p e + q e)) Sᶜ := by simpa [heq] using hkT
              have hlSafe := finiteTreeSafeRegion_closed_of_connected G
                (ofEdgeFun G (fun e => p e + q e)) Sᶜ hkSafe hconn
              exact (hlT (by simpa [heq] using hlSafe)).elim
            · exact False.elim
        rw [hzero]
        exact mul_nonneg hcorrS hvac
    · have hzero : finiteTreeSafeRegionFiber G beta J Sᶜ T {k, l} ∅ = 0 := by
        unfold finiteTreeSafeRegionFiber
        rw [gatedSourcePairSum_congr_sources G beta J {k, l} ∅
          (fun n => finiteTreeSafeRegion G n Sᶜ = T) (fun _ => False)]
        · unfold gatedSourcePairSum
          simp
        · intro p q hp hq
          constructor
          · intro heq
            apply hTS
            intro v hv
            have hvSafe : v ∈ finiteTreeSafeRegion G
                (ofEdgeFun G (fun e => p e + q e)) Sᶜ := by simpa [heq] using hv
            have hvCompl := finiteTreeSafeRegion_subset_compl G
              (ofEdgeFun G (fun e => p e + q e)) Sᶜ hvSafe
            simpa using hvCompl
          · exact False.elim
      rw [hzero]
      exact mul_nonneg hcorrS hvac
  · rw [if_neg hkT]
    exact mul_nonneg hcorrS hvac

end StatMech.FrontierA
