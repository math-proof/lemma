/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DisjointGraphFactorizeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxReduce.Part2
import Theorem.StatisticalMechanics.Code.FK.FKWiredDomainMonotone.Part2
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
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


variable {V : Type*} [Fintype V] [DecidableEq V] (G C : SimpleGraph V)
  [DecidableRel G.Adj] [DecidableRel C.Adj]


theorem dgf_disjoint_product_dom_doubleCap {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {F : Finset (Sym2 V)} (C' : SimpleGraph V) [DecidableRel C'.Adj] (hCC' : C ≤ C')
    {A B : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) (hB : DependsOnOutside F B)
    {α β : ℝ} (hα : 0 ≤ α)
    (hAcap : ∀ ψ ∈ fibreReps F,
      (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C' p q F ψ ρ) ≤ α)
    (hBcap : (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ) ≤ β) :
    (∑ ρ, (A ∩ B).indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ) ≤ α * β := by
  have hAB := bcProb_disjoint_product_dom_wired G C hp hp1 hq C' hCC' hA hB hα hAcap
  exact hAB.trans (mul_le_mul_of_nonneg_left hBcap hα)


theorem dgf_boxMultiOpen_dependsOnOutside (M : ℕ) (F : Finset (Sym2 (boxVerts d M)))
    (t : Finset (Sym2 (boxVerts d M))) (hdisj : ∀ e ∈ t, e ∉ F) :
    DependsOnOutside F (cdc_boxMultiOpenEvent M t) := by
  intro ψ ρ hagree
  constructor
  · intro hψ eb heb; rw [hagree eb (hdisj eb heb)]; exact hψ eb heb
  · intro hρ eb heb; rw [← hagree eb (hdisj eb heb)]; exact hρ eb heb


theorem dgf_cross_eq_boxRestrict_inter (M : ℕ) (g : Multiplicative (Site d))
    (T T' : Finset (Sym2 (Site d)))
    (tT tT' : Finset (Sym2 (boxVerts d M)))
    (hT : T = tT.image (edgeIncl d M))
    (hT' : T'.image (fun e => g⁻¹ • e) = tT'.image (edgeIncl d M)) :
    (fmu_multiOpen T ∩
        (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
          ⁻¹' fmu_multiOpen T')
      = boxRestrict d M ⁻¹' (cdc_boxMultiOpenEvent M tT ∩ cdc_boxMultiOpenEvent M tT') := by
  rw [fmu_shift_multiOpen g T', hT', hT,
    ftb_fmu_eq_cdc_multiOpen, ftb_fmu_eq_cdc_multiOpen,
    cdc_multiOpenEvent_image_eq_boxRestrict, cdc_multiOpenEvent_image_eq_boxRestrict,
    Set.preimage_inter]


end FK
end StatMech
