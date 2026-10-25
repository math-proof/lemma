/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc23allconn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc22edgecopy.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc21fiberconn.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc20closure.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc19switching.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc18core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc16core.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc6_munonneg
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Def.StatisticalMechanics.Code.Walls.gc23allconn
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc23_allConnResidue_iff_fifthDomination (β h : ℝ) (o x y : V) :
    gc23_fifthDomination G β h o x y ↔ gc22_AllConnResidue G β h o x y := by
  constructor
  · intro hdom m hm hOg
    have h5 := hdom m hm hOg
    linarith
  · intro hres m hm hOg
    have h5 := hres m hm hOg
    linarith


theorem gc23_cert_of_fifthDomination (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hdom : gc23_fifthDomination G β h o x y) :
    gc16_PerConfigCert G β h o x y :=
  gc22_cert_of_allConnResidue G β h hβ hh o x y hox hoy hxy
    ((gc23_allConnResidue_iff_fifthDomination G β h o x y).mp hdom)


theorem gc23_ursell_nonpos_of_fifthDomination (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hdom : gc23_fifthDomination G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc16_cert_closes_u3 G β h o x y hox hoy hxy
    (gc23_cert_of_fifthDomination G β h hβ hh o x y hox hoy hxy hdom)


theorem gc23_deficit_reorg (β h : ℝ) (o x y : V) (m : ↥(withGhost G).edgeFinset → ℕ) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
      = ∑ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
          (if sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅
            then weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) K₂.1)
            else 0)
            * (hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                  (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, none}
                + hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                    (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some x}
                + hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                    (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some y}
                - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                    (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) ∅) := by
  have h4 := gc18_firstFour_reorg G β h o x y m
  rw [show
      gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
      = -(gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
          - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
          - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
          - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y})
      from by ring]
  rw [h4, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun K₂ _ => ?_)
  ring


theorem gc23_fifthDomination_of_fifthVanish (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V)))
    (hT4 : gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m
        {some o, none} {some x, none} = 0) :
    2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none}
      ≤ gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ := by
  have hdef := gc23_firstFour_nonpos_uncond G β h hβ hh o x y hox hoy hxy m hbdry
  rw [hT4]; linarith

end StatMech.Walls
