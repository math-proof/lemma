/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Revealment.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part5
open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace RevealmentConstruction

open StatMech.OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]


variable {V : Type*} [DecidableEq V]


omit [Fintype E] in


theorem queried_exploreTree_imp (endU endV : E → V) (base : Finset V → Bool)
    (ω : ConfigSpace E) (B : Set V) (l : List E) (disc₀ : Finset V)
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (i : E)
    (hi : i ∈ (exploreTree endU endV base l disc₀).queried ω) :
    ConnOpenSet endU endV ω (endU i) B ∨ ConnOpenSet endU endV ω (endV i) B := by
  have hInv0 : geomInv endU endV ω B disc₀ :=
    fun x hx => connOpenSet_of_mem (hdisc₀ x hx)
  obtain ⟨τ, hτInv, hτg⟩ := mem_queried_buildTree (guard := geomGuard endU endV)
    (step := geomStep endU endV) (base := base) (Inv := geomInv endU endV ω B) (ω := ω)
    (fun σ e hσ hg => geomInv_step endU endV ω B σ e hσ hg) l disc₀ hInv0 i hi
  unfold geomGuard at hτg; simp only [decide_eq_true_eq] at hτg
  rcases hτg with hU | hV
  · exact Or.inl (hτInv _ hU)
  · exact Or.inr (hτInv _ hV)


theorem reveal_exploreTree_le {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (endU endV : E → V) (base : Finset V → Bool) (B : Set V) (l : List E) (disc₀ : Finset V)
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (i : E) :
    reveal ν (exploreTree endU endV base l disc₀) i
      ≤ expect ν (fun ω => if ConnOpenSet endU endV ω (endU i) B then (1 : ℝ) else 0)
        + expect ν (fun ω => if ConnOpenSet endU endV ω (endV i) B then (1 : ℝ) else 0) := by
  have h := revealment_le_of_queried_imp_or hν (exploreTree endU endV base l disc₀) i
    (fun ω => ConnOpenSet endU endV ω (endU i) B)
    (fun ω => ConnOpenSet endU endV ω (endV i) B)
    (fun ω hq => queried_exploreTree_imp endU endV base ω B l disc₀ hdisc₀ i hq)
  rwa [Revealment.revealment] at h


end RevealmentConstruction
end OSSS
end StatMech
