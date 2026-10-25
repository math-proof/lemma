/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc8core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc9Znormaliserpos
import Theorem.StatisticalMechanics.Code.Walls.gc9assembledDnonneg.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc9deltadef
import Theorem.StatisticalMechanics.Code.Walls.gc9Jnonneg
import Theorem.StatisticalMechanics.Code.Walls.gc9betaderivcov3
import Theorem.StatisticalMechanics.Code.Walls.gc9switching
import Theorem.StatisticalMechanics.Code.Walls.gc9eq15insertion
import Theorem.StatisticalMechanics.Code.Walls.gc6_ghostgraph
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Def.StatisticalMechanics.Code.Walls.gc9core.Part2
open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Sharpness.FieldGhostDict

open StatMech.Sharpness.GhostCurrentRep

open StatMech.Sharpness.FluxEdgeCopy (sourcePairDisconnSum sourcePairDisconnSum_eq_edgecopy)

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem gc9_deltaEdge_mk (β h : ℝ) (o x y : V) :
    gc9_deltaEdge G β h o s(x, y)
      = sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∅ (some o) none := rfl


theorem gc9_eq20_perEdge_cov3 (β h : ℝ) (o : V) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) (hoe : o ∉ e) :
    gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) * cov3sym G β h o e
      = gc9_deltaEdge G β h o e := by
  induction e with
  | h x y =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hxy : x ≠ y := G.ne_of_adj he
    have hox : o ≠ x := fun h => hoe (by rw [h]; exact Sym2.mem_mk_left x y)
    have hoy : o ≠ y := fun h => hoe (by rw [h]; exact Sym2.mem_mk_right x y)
    rw [gc9_deltaEdge_mk]
    exact gc9_eq20_perBond_cov3 G β h o x y hox hoy hxy


theorem gc9_eq20_pivotalMass_sum (β h : ℝ) (o : V) :
    gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1))
        * (∑ e ∈ G.edgeFinset.filter (fun e => o ∉ e), cov3sym G β h o e)
      = ∑ e ∈ G.edgeFinset.filter (fun e => o ∉ e), gc9_deltaEdge G β h o e := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [Finset.mem_filter] at he
  exact gc9_eq20_perEdge_cov3 G β h o he.1 he.2


theorem gc9_eq20_pivotalMass_sum_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    0 ≤ ∑ e ∈ G.edgeFinset.filter (fun e => o ∉ e), gc9_deltaEdge G β h o e := by
  refine Finset.sum_nonneg (fun e he => ?_)
  induction e with
  | h x y => rw [gc9_deltaEdge_mk]; exact gc9_eq20_pivotalMass_nonneg G β h hβ hh o x y


theorem gc9_eq20_derivative_identity (β h : ℝ) (o : V) :
    gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1))
        * deriv (fun β => isingExpectation G β h (fun s => spin s o)) β
      = gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1))
            * (∑ e ∈ G.edgeFinset.filter (fun e => o ∈ e), cov3sym G β h o e)
          + (∑ e ∈ G.edgeFinset.filter (fun e => o ∉ e), gc9_deltaEdge G β h o e)
          + gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1))
              * (h * susceptibility G β h o) := by
  rw [gc9_beta_deriv_cov3 G β h o]
  unfold bondEnergySusceptibility
  
  rw [← Finset.sum_filter_add_sum_filter_not G.edgeFinset (fun e => o ∈ e) (cov3sym G β h o)]
  
  have hpiv := gc9_eq20_pivotalMass_sum G β h o
  
  rw [mul_add]
  linarith [hpiv]


theorem gc9_cov3_degenerate_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o y : V) (hoy : o ≠ y) :
    0 ≤ cov3sym G β h o s(o, y) := by
  rw [cov3sym_mk]
  have h1 : isingExpectation G β h (fun s => spin s o * (spin s o * spin s y))
      = isingExpectation G β h (fun s => spin s y) := by
    congr 1; funext s
    rw [show spin s o * (spin s o * spin s y) = (spin s o * spin s o) * spin s y from by ring,
        spin_sq, one_mul]
  rw [h1]
  have hg := gks_second G β h hβ hh ({o} : Finset V) ({o, y} : Finset V)
  have hAB : ({o} : Finset V) ∆ ({o, y} : Finset V) = {y} := by
    ext z; simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
    constructor
    · rintro (⟨rfl, hn⟩ | ⟨hz, hn⟩)
      · exact absurd (Or.inl rfl) hn
      · rcases hz with rfl | rfl
        · exact absurd rfl hn
        · rfl
    · rintro rfl; exact Or.inr ⟨Or.inr rfl, fun hh => hoy hh.symm⟩
  rw [hAB] at hg
  have e1 : isingExpectation G β h (spinProd ({o} : Finset V))
      = isingExpectation G β h (fun s => spin s o) := by
    congr 1; funext s; unfold spinProd; rw [Finset.prod_singleton]
  have e2 : isingExpectation G β h (spinProd ({o, y} : Finset V))
      = isingExpectation G β h (fun s => spin s o * spin s y) := by
    congr 1; funext s; unfold spinProd; rw [Finset.prod_insert (by simp [hoy]), Finset.prod_singleton]
  have e3 : isingExpectation G β h (spinProd ({y} : Finset V))
      = isingExpectation G β h (fun s => spin s y) := by
    congr 1; funext s; unfold spinProd; rw [Finset.prod_singleton]
  rw [e1, e2, e3] at hg
  linarith [hg]


theorem gc9_cov3_edge_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) :
    0 ≤ cov3sym G β h o e := by
  induction e with
  | h x y =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hxy : x ≠ y := G.ne_of_adj he
    by_cases hox : o = x
    · subst hox; exact gc9_cov3_degenerate_nonneg G β h hβ hh o y hxy
    · by_cases hoy : o = y
      · subst hoy
        rw [Sym2.eq_swap]
        exact gc9_cov3_degenerate_nonneg G β h hβ hh o x hox
      · exact gc9_cov3_nonneg_of_eq20 G β h hβ hh o x y hox hoy hxy


theorem gc9_cov2_self_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    0 ≤ cov2 G β h o o := by
  unfold cov2
  have h1 : isingExpectation G β h (fun s => spin s o * spin s o) = 1 := by
    rw [show (fun s => spin s o * spin s o) = (fun _ : ConfigSpace V => (1 : ℝ)) from by
      funext s; exact spin_sq s o]
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have hg := gks_second G β h hβ hh ({o} : Finset V) ({o} : Finset V)
  rw [symmDiff_self] at hg
  have eo : isingExpectation G β h (spinProd ({o} : Finset V))
      = isingExpectation G β h (fun s => spin s o) := by
    congr 1; funext s; unfold spinProd; rw [Finset.prod_singleton]
  have eb : isingExpectation G β h (spinProd (⊥ : Finset V)) = 1 := by
    rw [show (⊥ : Finset V) = (∅ : Finset V) from rfl,
        show spinProd (∅ : Finset V) = (fun _ : ConfigSpace V => (1 : ℝ)) from by
          funext s; exact spinProd_empty s]
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  rw [eo, eb] at hg
  rw [h1]
  linarith [hg]


theorem gc9_susceptibility_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    0 ≤ susceptibility G β h o := by
  unfold susceptibility
  refine Finset.sum_nonneg (fun x _ => ?_)
  by_cases hox : o = x
  · subst hox; exact gc9_cov2_self_nonneg G β h hβ hh o
  · exact StatMech.Ising.cov2_nonneg G β h hβ hh o x hox


theorem gc9_beta_deriv_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    0 ≤ deriv (fun β => isingExpectation G β h (fun s => spin s o)) β := by
  rw [gc9_beta_deriv_cov3 G β h o]
  refine add_nonneg ?_ (mul_nonneg hh (gc9_susceptibility_nonneg G β h hβ hh o))
  exact Finset.sum_nonneg (fun e he => gc9_cov3_edge_nonneg G β h hβ hh o he)


end StatMech.Walls
