/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentMeasures
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSources.Part3
import Instance.StatisticalMechanics.Code.FrontierB.FiniteCurrentParity
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def freeParityRawMass (beta : ℝ)
    (H : Finset (Sym2 V)) : ENNReal :=
  ENNReal.ofReal
    (if H ⊆ G.edgeFinset ∧ IsEvenSubgraph H then
      Real.tanh beta ^ H.card else 0)

noncomputable def freeParityPMF (beta : ℝ) (_hbeta : 0 ≤ beta) :
    PMF (Finset (Sym2 V)) :=
  PMF.normalize (freeParityRawMass G beta)
    (by
      rw [tsum_fintype]
      have hone : freeParityRawMass G beta ∅ = 1 := by
        simp [freeParityRawMass, IsEvenSubgraph, incCount]
      intro hzero
      have hle : freeParityRawMass G beta ∅ ≤
          ∑ H : Finset (Sym2 V), freeParityRawMass G beta H :=
        Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ ∅)
      rw [hzero, hone] at hle
      exact one_ne_zero (bot_unique hle))
    (by
      rw [tsum_fintype]
      exact ENNReal.sum_ne_top.2 fun H _ => ENNReal.ofReal_ne_top)

noncomputable def freeParityMeasure (beta : ℝ) (hbeta : 0 ≤ beta) :
    ProbabilityMeasure (Finset (Sym2 V)) :=
  ⟨(freeParityPMF G beta hbeta).toMeasure, inferInstance⟩

end StatMech.FrontierB
