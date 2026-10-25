/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part4
import Def.StatisticalMechanics.Code.FK.LimitCommutation.Part3
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}


theorem lmc_wiredMultiHomogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (hplace : lmc_wiredPlacement hp hp1 g) :
    cdc_wiredMultiHomogeneous hp hp1 g := by
  intro s
  obtain ⟨N, t, hst, hcofinal⟩ := hplace s
  subst hst
  
  exact lmc_wiredMultiHomogeneous_of_cofinal (Multiplicative.toAdd g⁻¹) N t hp hp1 hcofinal


theorem lmc_wiredPlacement_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    lmc_wiredPlacement hp hp1 (1 : Multiplicative (Site d)) := by
  intro s
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  refine ⟨N, t, hst, ?_⟩
  
  have hs : s.image (fun e => (1 : Multiplicative (Site d))⁻¹ • e) = t.image (edgeIncl d N) := by
    rw [hst, Finset.image_image]
    refine Finset.image_congr fun eb _ => ?_
    simp only [Function.comp_apply, inv_one, one_smul]
  rw [hs]
  exact lmc_transBoxMass_tendsto_centred_iv (Multiplicative.toAdd (1 : Multiplicative (Site d))⁻¹)
    N t hp hp1


theorem lmc_wiredMultiHomogeneous_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    cdc_wiredMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) :=
  lmc_wiredMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) (lmc_wiredPlacement_one hp hp1)


theorem lmc_wiredIV_isTranslationInvariant_of_placement {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hplace : ∀ g : Multiplicative (Site d), lmc_wiredPlacement hp hp1 g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  cdc_wiredIV_isTranslationInvariant_of_homogeneous hp hp1
    (fun g _ _ _ => lmc_wiredMultiHomogeneous hp hp1 g (hplace g))


end FK
end StatMech
