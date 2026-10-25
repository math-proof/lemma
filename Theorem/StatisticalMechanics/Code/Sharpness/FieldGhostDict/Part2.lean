/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Def.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part2
open Finset SimpleGraph
open scoped symmDiff
open StatMech StatMech.Ising StatMech.Sharpness

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem ghostCoupling_some_some (h β : ℝ) (J : Sym2 V → ℝ) (x y : V) :
    ghostCoupling h β J s(some x, some y) = J s(x, y) := rfl

@[simp] theorem ghostCoupling_some_none (h β : ℝ) (J : Sym2 V → ℝ) (x : V) :
    ghostCoupling h β J s(some x, none) = h := rfl


theorem bond_map_some (s : ConfigSpace (Option V)) (e : Sym2 V) :
    bond s (Sym2.map some e) = bond (fun x => s (some x)) e := by
  induction e with | h x y => rw [Sym2.map_mk, bond_mk, bond_mk]; rfl


theorem ghost_bondSum (h β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace (Option V)) :
    (∑ e ∈ (withGhost G).edgeFinset, ghostCoupling h β J e * bond s e)
      = (∑ e ∈ G.edgeFinset, J e * bond s (Sym2.map some e))
        + h * spin s none * ∑ x : V, spin s (some x) := by
  rw [withGhost_edgeFinset_eq, Finset.sum_union (disjoint_orig_ghost G)]
  congr 1
  · rw [origEdges, Finset.sum_image]
    · refine Finset.sum_congr rfl (fun e _ => ?_)
      induction e with
      | h x y => rw [Sym2.map_mk]; simp only [ghostCoupling_some_some]
    · intro a _ b _ hab; exact Sym2.map.injective (Option.some_injective V) hab
  · rw [ghostEdges, Finset.sum_image]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [ghostCoupling_some_none, bond_mk]; ring
    · intro a _ b _ hab
      rw [Sym2.eq_iff] at hab; rcases hab with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact Option.some_injective V h1
      · exact absurd h2 (by simp)


theorem fgd_ghost_weight_eq (β h : ℝ) (s : ConfigSpace (Option V)) :
    boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) s
      = isingWeight G β (h * spin s none) (fun z => s (some z)) := by
  unfold boltzmannJ isingWeight hamiltonian
  rw [ghost_bondSum]
  congr 1
  have hbond : (∑ e ∈ G.edgeFinset, (1 : ℝ) * bond s (Sym2.map some e))
      = ∑ e ∈ G.edgeFinset, bond (fun z => s (some z)) e :=
    Finset.sum_congr rfl (fun e _ => by rw [one_mul, bond_map_some])
  have hspin : (∑ x : V, spin s (some x)) = ∑ x : V, spin (fun z => s (some z)) x := rfl
  rw [hbond, hspin]; ring


end FieldGhostDict
end Sharpness
end StatMech
