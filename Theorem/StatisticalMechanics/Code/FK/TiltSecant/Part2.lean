/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TiltSecant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose3
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Def.StatisticalMechanics.Code.FK.TiltSecant
open MeasureTheory Set Filter Topology Real
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


theorem hsecant_discharged (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hdata : FKSecantData d N eb) :
    ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p'
        ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p := by
  obtain ⟨S, V, hVpos, hSV, hVinf, hineq⟩ := hdata
  intro p hp p' hp' hlt
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hp'0, hp'1⟩ := hp'
  
  have hlampos : 0 < tiltFactor p p' :=
    tiltFactor_pos hp0 hp1 hp'0 hp'1
  have hlam1 : tiltFactor p p' < 1 :=
    tiltFactor_lt_one hp0 hp1 hlt
  
  exact secant_b_le_a_of_finiteVolumeData (q := (2 : ℝ)) (by norm_num) hlampos hlam1
    hVpos hSV hVinf
    (fun ε hε n => hineq p ⟨hp0, hp1⟩ p' ⟨hp'0, hp'1⟩ hlt ε hε n)


theorem fk_uniqueness_q2_secant_from_finiteVolumeData (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hdata : FKSecantData d N eb) :
    ∃ S : Set ℝ, S.Countable ∧
      ∀ p ∉ S, ∀ (hp : 0 < p) (hp1 : p < 1)
        (phi : Measure (ConfigSpace (Sym2 (Site d)))),
        ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
            (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ≤ phi.real
              (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
          ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
              ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
                  (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))) →
        phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
            = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
                (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
          ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
              = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
                  (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) :=
  fk_uniqueness_off_countable_q2_full d N eb (hsecant_discharged d N eb hdata)

end FK
end StatMech
