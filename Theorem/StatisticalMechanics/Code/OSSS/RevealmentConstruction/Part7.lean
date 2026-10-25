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
import Def.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part6
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


section Lattice

variable {d : ℕ}


omit [DecidableEq E] [DecidableEq V] in

theorem liftCfg_apply_edge {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    (ω : ConfigSpace E) (e : E) : liftCfg edge ω (edge e) = ω e := by
  unfold liftCfg
  have hex : ∃ e', edge e' = edge e := ⟨e, rfl⟩
  rw [dif_pos hex]; congr 1; exact hinj hex.choose_spec

omit [DecidableEq E] [DecidableEq V] in


theorem reachOpen_imp_connected {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} {ω : ConfigSpace E}
    (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    {x y : Site d} (h : ReachOpen endU endV ω x y) :
    Connected d (liftCfg edge ω) x y := by
  induction h with
  | refl x => exact connected_refl _ x
  | step e hopen hpair _ ih =>
      have hedgeopen : liftCfg edge ω (edge e) = true := by
        rw [liftCfg_apply_edge hinj]; exact hopen
      have hopenUV : IsOpenEdge d (liftCfg edge ω) (endU e) (endV e) := by
        refine ⟨hadj e, ?_⟩; rw [← hcoh e]; exact hedgeopen
      rcases hpair with ⟨hU, hV⟩ | ⟨hU, hV⟩
      · subst hU; subst hV; exact (IsOpenEdge.connected hopenUV).trans ih
      · subst hU; subst hV; exact (IsOpenEdge.connected (isOpenEdge_symm hopenUV)).trans ih

omit [DecidableEq E] [DecidableEq V] in

theorem connOpenSet_imp_connectedToSet {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    {ω : ConfigSpace E} {x : Site d} {B : Set (Site d)}
    (h : ConnOpenSet endU endV ω x B) : ConnectedToSet d (liftCfg edge ω) x B := by
  obtain ⟨b, hbB, hreach⟩ := h
  exact ⟨b, hbB, reachOpen_imp_connected hinj hcoh hadj hreach⟩


theorem expect_indicator_mono {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (P Q : ConfigSpace E → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ ω, P ω → Q ω) :
    expect ν (fun ω => if P ω then (1 : ℝ) else 0)
      ≤ expect ν (fun ω => if Q ω then (1 : ℝ) else 0) := by
  apply expect_mono hν
  intro ω
  by_cases hp : P ω
  · rw [if_pos hp, if_pos (h ω hp)]
  · rw [if_neg hp]; split <;> norm_num


theorem reveal_exploreTree_le_connected {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (base : Finset (Site d) → Bool) (B : Set (Site d)) (l : List E) (disc₀ : Finset (Site d))
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (i : E) :
    reveal ν (exploreTree endU endV base l disc₀) i
      ≤ expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU i) B then (1 : ℝ) else 0)
        + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV i) B then (1 : ℝ) else 0) := by
  refine le_trans (reveal_exploreTree_le hν endU endV base B l disc₀ hdisc₀ i) ?_
  apply add_le_add
  · exact expect_indicator_mono hν _ _
      (fun ω hP => connOpenSet_imp_connectedToSet hinj hcoh hadj hP)
  · exact expect_indicator_mono hν _ _
      (fun ω hP => connOpenSet_imp_connectedToSet hinj hcoh hadj hP)

end Lattice


omit [Fintype E] [DecidableEq E] in


theorem runState_geomInv (endU endV : E → V) (ω : ConfigSpace E) (B : Set V)
    (l : List E) (disc₀ : Finset V) (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) :
    geomInv endU endV ω B (runState (geomGuard endU endV) (geomStep endU endV) ω l disc₀) :=
  runState_inv (guard := geomGuard endU endV) (step := geomStep endU endV)
    (Inv := geomInv endU endV ω B) (ω := ω)
    (fun σ e hσ hg => geomInv_step endU endV ω B σ e hσ hg) l disc₀
    (fun x hx => connOpenSet_of_mem (hdisc₀ x hx))

omit [Fintype E] [DecidableEq E] in


theorem eval_exploreTree_imp_conn (endU endV : E → V) (o : V) (B : Set V)
    (l : List E) (disc₀ : Finset V) (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
    (ω : ConfigSpace E)
    (h : (exploreTree endU endV (fun disc => decide (o ∈ disc)) l disc₀).eval ω = true) :
    ConnOpenSet endU endV ω o B := by
  rw [exploreTree, eval_buildTree] at h
  simp only [decide_eq_true_eq] at h
  exact runState_geomInv endU endV ω B l disc₀ hdisc₀ o h

end RevealmentConstruction
end OSSS
end StatMech
