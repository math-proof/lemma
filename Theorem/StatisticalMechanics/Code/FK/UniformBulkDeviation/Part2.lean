/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.SpatialCollapse
import Theorem.StatisticalMechanics.Code.FK.OneSidedContinuity
import Theorem.StatisticalMechanics.Code.FK.WiredPressureDeriv.Part4
import Theorem.StatisticalMechanics.Code.FK.FKDensityDeriv.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose3
import Theorem.StatisticalMechanics.Code.FK.FKLimitsClose.Part3
import Def.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

variable {d : ℕ}


theorem ubd_freeGrowingBoxCollapse_of_uniformBulk (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hubd : ubd_FreeUniformBulkDeviation (d := d) N) :
    ubd_FreeGrowingBoxCollapse (d := d) N := by
  intro e' t
  obtain ⟨In, δ, hIE, hδ0, hδlim, hin, hbdy⟩ := hubd e' t
  obtain ⟨hL0, hL1⟩ := ubd_freeEdgeDensity_mem_Icc N e' t
  exact spc_growingBox_collapse t hEbox _ hL0 hL1 In hIE δ hδ0 hδlim hin hbdy


theorem ubd_wiredGrowingBoxCollapse_of_uniformBulk (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hubd : ubd_WiredUniformBulkDeviation (d := d) N) :
    wpd_AvgWiredDensityCollapse (d := d) N := by
  intro e' t
  obtain ⟨In, δ, hIE, hδ0, hδlim, hin, hbdy⟩ := hubd e' t
  obtain ⟨hL0, hL1⟩ := ubd_wiredEdgeDensity_mem_Icc N e' t
  exact ubd_growingBox_wiredCollapse t hEbox _ hL0 hL1 In hIE δ hδ0 hδlim hin hbdy


theorem ubd_fk_uniqueness_of_uniformBulk (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hfreeBulk : ubd_FreeUniformBulkDeviation (d := d) N)
    (hwiredBulk : ubd_WiredUniformBulkDeviation (d := d) N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  ubd_fk_uniqueness_of_growingBoxCollapse hd N eb hEbox hg hboxfree
    (ubd_freeGrowingBoxCollapse_of_uniformBulk N hEbox hfreeBulk)
    (ubd_wiredGrowingBoxCollapse_of_uniformBulk N hEbox hwiredBulk)


theorem ubd_wiredEdgeDensity_translation_invariant {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (e : Sym2 (Site d)) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent {e})
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (({e} : Finset (Sym2 (Site d))).image (fun e => g⁻¹ • e))) :=
  flc_wiredMultiHomogeneous hp hp1 g {e}


theorem ubd_residue_remark : True := trivial

end FK
end StatMech
