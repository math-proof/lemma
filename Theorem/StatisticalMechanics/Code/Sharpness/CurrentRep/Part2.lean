/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Def.StatisticalMechanics.Code.Sharpness.CurrentRep
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000


namespace StatMech

namespace Sharpness

open StatMech.Ising


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem weight_ofEdgeFun (β : ℝ) (J : Sym2 V → ℝ) (m : ↥G.edgeFinset → ℕ) :
    weight G β J (ofEdgeFun G m)
      = ∏ e : ↥G.edgeFinset, (β * J e.1) ^ (m e) / (Nat.factorial (m e)) := by
  unfold weight ofEdgeFun
  rw [← Finset.prod_attach G.edgeFinset
      (fun e => (β * J e) ^ (if h : e ∈ G.edgeFinset then m ⟨e, h⟩ else 0)
        / (Nat.factorial (if h : e ∈ G.edgeFinset then m ⟨e, h⟩ else 0)))]
  exact Finset.prod_congr rfl (fun e _ => by rw [dif_pos e.2])


theorem prod_bond_pow_ofEdgeFun (s : ConfigSpace V) (m : ↥G.edgeFinset → ℕ) :
    (∏ e ∈ G.edgeFinset, (bond s e) ^ ((ofEdgeFun G m) e))
      = ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e) := by
  rw [← Finset.prod_attach G.edgeFinset (fun e => (bond s e) ^ ((ofEdgeFun G m) e))]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  unfold ofEdgeFun; rw [dif_pos e.2]


end Sharpness
end StatMech
