/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
import Theorem.StatisticalMechanics.Code.FK.FKLimitsClose.Part3
import Def.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false


namespace StatMech

namespace FK

variable {d : ℕ}


variable {Sin Sout : Set (Site d)}


theorem bdp_freeUniformBulkDeviation_of_sandwich (N : ℕ)
    (hsand : bdp_FreeOffCentreSandwich (d := d) N) :
    ubd_FreeUniformBulkDeviation (d := d) N := by
  intro e' t
  obtain ⟨In, δ, hIE, hδ0, hδlim, hhom, hlow, hbdy⟩ := hsand e' t
  refine ⟨In, δ, hIE, hδ0, hδlim, ?_, hbdy⟩
  intro n e he
  set L := freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) with hL
  
  have hup : edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e ≤ L := by
    rw [← hhom n e he]
    exact bdp_free_per_edge_upper n e (fsc_logistic_pos t) (fsc_logistic_lt_one t)
  
  have hlo : L - δ n ≤ edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e := hlow n e he
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩


theorem bdp_wiredUniformBulkDeviation_of_sandwich (N : ℕ)
    (hsand : bdp_WiredOffCentreSandwich (d := d) N) :
    ubd_WiredUniformBulkDeviation (d := d) N := by
  intro e' t
  obtain ⟨In, δ, hIE, hδ0, hδlim, hhom, hup, hbdy⟩ := hsand e' t
  refine ⟨In, δ, hIE, hδ0, hδlim, ?_, hbdy⟩
  intro n e he
  set L := wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) with hL
  
  have hlo : L ≤ edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e := by
    rw [← hhom n e he]
    exact bdp_wired_per_edge_lower n e (fsc_logistic_pos t) (fsc_logistic_lt_one t)
  
  have hupb : edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e
      ≤ L + δ n := hup n e he
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩


theorem bdp_fk_uniqueness_of_offCentreSandwich (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hfreeSand : bdp_FreeOffCentreSandwich (d := d) N)
    (hwiredSand : bdp_WiredOffCentreSandwich (d := d) N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  ubd_fk_uniqueness_of_uniformBulk hd N eb hEbox hg hboxfree
    (bdp_freeUniformBulkDeviation_of_sandwich N hfreeSand)
    (bdp_wiredUniformBulkDeviation_of_sandwich N hwiredSand)

end FK
end StatMech
