/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part4
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Def.StatisticalMechanics.Code.Ising.GHSLebowitz.Part3
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsL_duplicateWeight_eq_tWeight_mul_uWeight (β h : ℝ)
    (q a : ConfigSpace V) :
    isingWeight G β h a * isingWeight G β h (ghsLMate q a) =
      ghsLTWeight G β h q a * ghsLUWeight G β q a := by
  unfold isingWeight ghsLTWeight ghsLUWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hb := ghsL_bondSum_split G q a
  have hs := ghsL_spinSum_split q a
  calc
    -β * hamiltonian G h a + -β * hamiltonian G h (ghsLMate q a) =
        β * ((∑ e ∈ G.edgeFinset, bond a e) +
          ∑ e ∈ G.edgeFinset, bond (ghsLMate q a) e) +
        β * h * ((∑ v : V, spin a v) + ∑ v : V, spin (ghsLMate q a) v) := by
      unfold hamiltonian
      ring
    _ = 2 * β *
          ((∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q), bond a e) +
            h * ∑ v ∈ ghsLAgreeFinset q, spin a v) +
        2 * β * ∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ, bond a e := by
      rw [hb, hs]
      ring


end Ising
end StatMech
