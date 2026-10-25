/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.IsingFK.Coloring.Part6
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem esJointProb_incompatible {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V))
    (h : ¬ Compatible G σ ω) : esJointProb G q p σ ω = 0 := by
  unfold esJointProb
  rw [esWeight_eq_of_compatible, if_neg h, zero_div]


theorem esJointProb_compatible {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V))
    (h : Compatible G σ ω) :
    esJointProb G q p σ ω
      = (p ^ openCount G ω * (1 - p) ^ closedCount G ω) / fkZ G p (q : ℝ) := by
  unfold esJointProb
  rw [esWeight_eq_of_compatible, if_pos h, esZ_eq_fkZ, edgeProduct_eq_pow]


theorem esJointProb_eq {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    esJointProb G q p σ ω
      = if Compatible G σ ω then
          (p ^ openCount G ω * (1 - p) ^ closedCount G ω) / fkZ G p (q : ℝ)
        else 0 := by
  by_cases h : Compatible G σ ω
  · rw [if_pos h, esJointProb_compatible G p σ ω h]
  · rw [if_neg h, esJointProb_incompatible G p σ ω h]

end IsingFK
end StatMech
