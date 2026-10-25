/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.PrefixCoversClose.Part3
import Theorem.StatisticalMechanics.Code.OSSS.FKRevealmentClose
import Def.StatisticalMechanics.Code.OSSS.PerScaleRevealmentClose.Part2
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace PerScaleRevealmentClose

open OSSS.Coding

open OSSS.AdaptMConditional

open StatMech.OSSS

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.ReachDomination

open StatMech.OSSS.RevealmentBoxCrossing

open StatMech.OSSS.PrefixCoversClose

open StatMech.OSSS.FKRevealmentClose

open StatMech.OSSS.MonotonicFK

open StatMech.Lattice

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


theorem psr_frontierConn_first_false_concrete (σ : Fin 3 ≃ Fin 3) (he₀ : (σ.symm 0 : ℕ) = 0) :
    ¬ FrontierConn σ
        (indicatorConn psr_witnessEndU psr_witnessEndV ({0} : Set (Fin 4)) ({3} : Set (Fin 4)))
        psr_witnessEndU psr_witnessEndV ({0} : Set (Fin 4)) (0 : Fin 3) := by
  refine psr_frontierConn_first_refutable_witness σ psr_witnessEndU psr_witnessEndV
    ({0} : Set (Fin 4)) ({3} : Set (Fin 4)) he₀
    (fun _ => false) (fun _ => true) ?_ ?_ ?_ ?_
  · rintro ⟨x, hxC, b, hbB, hreach⟩
    simp only [Set.mem_singleton_iff] at hxC hbB
    have := psr_reachOpen_allClosed hreach; omega
  · refine ⟨3, Set.mem_singleton 3, 0, Set.mem_singleton 0, ?_⟩
    refine ReachOpen.step 2 rfl (Or.inr ⟨rfl, rfl⟩) ?_
    refine ReachOpen.step 0 rfl (Or.inr ⟨rfl, rfl⟩) ?_
    refine ReachOpen.step 1 rfl (Or.inr ⟨rfl, rfl⟩) ?_
    exact ReachOpen.refl 0
  · rintro ⟨b, hbB, hreach⟩
    simp only [Set.mem_singleton_iff] at hbB
    have := psr_reachOpen_allClosed hreach
    simp only [psr_witnessEndU, Matrix.cons_val_zero] at this; omega
  · rintro ⟨b, hbB, hreach⟩
    simp only [Set.mem_singleton_iff] at hbB
    have := psr_reachOpen_allClosed hreach
    simp only [psr_witnessEndV, Matrix.cons_val_zero] at this; omega

end PerScaleRevealmentClose
end OSSS
end StatMech
