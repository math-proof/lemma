/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc6_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc8crossingallconn
import Theorem.StatisticalMechanics.Code.Walls.gc8innereq15
import Theorem.StatisticalMechanics.Code.Walls.gc8reinnerpair
import Theorem.StatisticalMechanics.Code.Walls.gc8Z0pos
import Theorem.StatisticalMechanics.Code.Walls.gc8munonneg
import Theorem.StatisticalMechanics.Code.Walls.gc8fourmarks
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Def.StatisticalMechanics.Code.Walls.gc8core
open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


variable {ι : Type*} [DecidableEq ι] [Fintype ι]


theorem gc8_pivotalBridge_of_eqSwi (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hid : gc6_EqSwiIdentity G β h o) :
    gc8_PivotalSignBridge G β h o := by
  intro x y hox hoy hxy
  obtain ⟨J, μ, M, B, o', x', y', hβ', hJ, hμ, hox', hoy', hxy', hZpos, hident⟩ :=
    hid x y hox hoy hxy
  refine ⟨- (μ * egh_ensembleUrsell G β J M B o' x' y'), tcp_partitionFunction G β J M B,
    ?_, hZpos, ?_⟩
  · 
    rw [egh_ensemble_ursell_eq G β J M B hox' hoy' hxy']
    have hN : 0 ≤ tcp_allConnMass G β J M B o' x' y' :=
      tcp_allConnMass_nonneg G β J hβ' hJ M B o' x' y'
    nlinarith [hμ, hN]
  · rw [hident]; ring


theorem gc8_core_ursell_nonpos_distinct (β h : ℝ) (o : V)
    (hbr : gc8_PivotalSignBridge G β h o) (x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  obtain ⟨D, Z', hD, hZ, hid⟩ := hbr x y hox hoy hxy
  have hu : eg_ursell3 G β h o x y = - D / Z' := by
    rw [eq_div_iff (ne_of_gt hZ)]; linarith [hid]
  rw [hu]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hZ.le


theorem gc8_core_signDominance (β h : ℝ) (o : V)
    (hbr : gc8_PivotalSignBridge G β h o) :
    GHSSignDominance G β h o :=
  fun x y hox hoy hxy => gc8_core_ursell_nonpos_distinct G β h o hbr x y hox hoy hxy


theorem gc8_core_ursell_nonpos (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hbr : gc8_PivotalSignBridge G β h o) (x y : V) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc5_core_ursell_nonpos_of_signDominance G β h hβ hh o
    (gc8_core_signDominance G β h o hbr) x y


theorem gc8_core_ghs_concavity (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hbr : gc8_PivotalSignBridge G β h o) :
    GHSThreePointSym G β h o :=
  gc5_core_ghs_concavity_of_signDominance G β h hβ hh o
    (gc8_core_signDominance G β h o hbr)


theorem gc8_core_sharpness (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (Jc : ℝ)
    (hbr : gc8_PivotalSignBridge G β h o)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = Jc * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ Jc * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc5_core_aizenman_barsky_of_signDominance G β h hβ hh o Jc
    (gc8_core_signDominance G β h o hbr) hfactor


theorem gc8_core_bracket_surjective {μ t : ℝ} (hμ : 0 ≤ μ) (hlo : -2 * μ ≤ t) (hhi : t ≤ 0) :
    ∃ P : ℝ, 0 ≤ P ∧ P ≤ 1 ∧ -2 * μ * P = t :=
  gc6_core_bracket_surjective hμ hlo hhi


theorem gc8_core_pivotalBridge_iff_ursell_nonpos (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (∃ (D Z' : ℝ), (0 ≤ D) ∧ (0 < Z') ∧ eg_ursell3 G β h o x y * Z' = - D)
      ↔ eg_ursell3 G β h o x y ≤ 0 := by
  constructor
  · rintro ⟨D, Z', hD, hZ, hid⟩
    have hu : eg_ursell3 G β h o x y = - D / Z' := by
      rw [eq_div_iff (ne_of_gt hZ)]; linarith [hid]
    rw [hu]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hZ.le
  · intro hle
    exact ⟨- eg_ursell3 G β h o x y, 1, by linarith, one_pos, by ring⟩


theorem gc8_core_eqclaim_lower_bound_nonvacuous :
    0 ≤ (Sharpness.currentSum (⊥ : SimpleGraph (Fin 4)) 1 (fun _ => 1) ({1, 2} : Finset (Fin 4))) ^ 2
        / Sharpness.currentSum (⊥ : SimpleGraph (Fin 4)) 1 (fun _ => 1) ∅ :=
  gc8_core_claim1_eqclaim_lower_bound_nonneg (⊥ : SimpleGraph (Fin 4)) 1 (fun _ => 1) 1 2


theorem gc8_core_normaliser_nonneg_nonvacuous :
    0 ≤ isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1, 2, 0} : Finset (Fin 3)))
        * (isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({2} : Finset (Fin 3)))) ^ 2
        * isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1} : Finset (Fin 3)))
        * (Sharpness.currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1
            (ghostCoupling 1 1 (fun _ => 1)) ∅) ^ 2 :=
  gc8_core_claim1_normaliser_nonneg (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin 3)) 1 1
    (by norm_num) (by norm_num) 0 1 2 0 (ghostCoupling 1 1 (fun _ => 1))


theorem gc8_core_pivotalBridge_degenerate (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (x y : V)
    (hxy : x ≠ y) :
    ∃ (D Z' : ℝ), (0 ≤ D) ∧ (0 < Z') ∧ eg_ursell3 G β h x x y * Z' = - D := by
  refine ⟨- eg_ursell3 G β h x x y, 1, ?_, one_pos, by ring⟩
  have hle : eg_ursell3 G β h x x y ≤ 0 := gc_ursell_nonpos_degenerate G β h hβ hh x y hxy
  linarith


theorem gc8_core_consistent (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hid : gc6_EqSwiIdentity G β h o) :
    gc8_PivotalSignBridge G β h o :=
  gc8_pivotalBridge_of_eqSwi G β h hβ hh o hid

end StatMech.Walls
