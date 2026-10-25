/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxReduce.Part2
import Theorem.StatisticalMechanics.Code.FK.DisjointGraphFactorizeClose.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
open MeasureTheory Filter Topology Set SimpleGraph
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}


theorem cbk_boxVertInclLE_val {N m : ℕ} (h : N ≤ m) (x : boxVerts d N) :
    (boxVertInclLE d h x : Site d) = (x : Site d) := rfl


theorem cbk_boxVertInclLE_injective {N m : ℕ} (h : N ≤ m) :
    Function.Injective (boxVertInclLE d h) := by
  intro x y hxy
  apply Subtype.ext
  have := congrArg (Subtype.val) hxy
  simpa [boxVertInclLE] using this


theorem cbk_adjMatch {N m : ℕ} (h : N ≤ m) :
    ocd_AdjMatch (boxGraph d N) (boxGraph d m) (boxVertInclLE d h) :=
  ocd_latticeAdjMatch (boxVertInclLE d h) (cbk_boxVertInclLE_val h)


theorem cbk_margin {N m : ℕ} (hNm : N < m) (x : boxVerts d N) :
    ¬ boxBoundary d m (boxVertInclLE d (le_of_lt hNm) x) := by
  intro hbdry
  rw [boxBoundary, mem_vertexBoundary] at hbdry
  apply hbdry.2
  
  have hxN : (x : Site d) ∈ box d N := x.2
  exact box_mono d (by omega) hxN


theorem cbk_bdryIn {N : ℕ} (hN : 1 ≤ N) (x : boxVerts d N) (z : Site d)
    (hnn : NearestNeighbour d (x : Site d) z) (hz : z ∉ box d N) :
    boxBoundary d N x :=
  ⟨x.2, notMem_box_pred_of_adj_outer hN x.2 hnn hz⟩


theorem cbk_inducedWiring_le {N m : ℕ} (hN : 1 ≤ N) (hNm : N < m)
    (ψ : ConfigSpace (Sym2 (boxVerts d m))) :
    ocd_inducedWiring (boxGraph d m) (boxVertInclLE d (le_of_lt hNm)) (boxBoundary d m) ψ
      ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d N) :=
  ocd_latticeInducedWiring_le (boxVertInclLE d (le_of_lt hNm)) (cbk_boxVertInclLE_val _)
    (cbk_boxVertInclLE_injective _) (boxBoundary d m) (boxBoundary d N)
    (cbk_margin hNm) (fun x z => cbk_bdryIn hN x z) ψ


theorem cbk_condBcProb_innerRestrict_le {N m : ℕ} (hN : 1 ≤ N) (hNm : N < m)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 (boxVerts d m)))
    {A : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hA : IsIncreasing A) :
    (∑ ρ, (ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm)) ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ
        * condBcProb (boxGraph d m)
            (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d m)) p q
            (ocd_innerEdgeFinset (boxVertInclLE d (le_of_lt hNm))) ψ ρ)
      ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * wiredFkProb (boxGraph d N) (boxBoundary d N) p q ω :=
  ocd_condBcProb_innerRestrict_le (cbk_boxVertInclLE_injective (le_of_lt hNm))
    (cbk_adjMatch (le_of_lt hNm)) (boxBoundary d N) hp hp1 hq ψ
    (cbk_inducedWiring_le hN hNm ψ) hA


theorem cbk_nearMass_eq_sum (N : ℕ) (t : Finset (Sym2 (boxVerts d N))) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (t.image (edgeIncl d N)))
      = ∑ ω, (cdc_boxMultiOpenEvent N t).indicator (fun _ => (1:ℝ)) ω
          * wiredFkProb (boxGraph d N) (boxBoundary d N) p 2 ω := by
  rw [ftb_fmu_eq_cdc_multiOpen, cdc_multiOpenEvent_image_eq_boxRestrict N t]
  have hmeas : MeasurableSet (boxRestrict d N ⁻¹' (cdc_boxMultiOpenEvent N t)) :=
    (continuous_boxRestrict d N).measurable (MeasurableSet.of_discrete)
  rw [wiredFiniteMeasure_real_boxRestrictEvent N hp hp1 (cdc_boxMultiOpenEvent N t) hmeas]


theorem cbk_ocd_innerEdge_eq {N m : ℕ} (h : N ≤ m) :
    ocd_innerEdge (boxVertInclLE d h) = innerEdgeLE d h := rfl


theorem cbk_innerRestrict_preimage {N m : ℕ} (h : N ≤ m) (t : Finset (Sym2 (boxVerts d N))) :
    ocd_innerRestrict (boxVertInclLE d h) ⁻¹' (cdc_boxMultiOpenEvent N t)
      = cdc_boxMultiOpenEvent m (t.image (innerEdgeLE d h)) := by
  rw [show cdc_boxMultiOpenEvent N t = med_genericMultiOpenEvent t from rfl,
    ocd_innerRestrict_preimage_multiOpenEvent (cbk_boxVertInclLE_injective h) t,
    cbk_ocd_innerEdge_eq h]
  rfl


theorem cbk_boxMultiOpen_increasing (m : ℕ) (s : Finset (Sym2 (boxVerts d m))) :
    IsIncreasing (cdc_boxMultiOpenEvent m s) :=
  cdc_boxMultiOpenEvent_isIncreasing m s


end FK
end StatMech
