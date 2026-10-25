/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Def.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

@[simp] theorem oddBit_eq_true_iff (n : Nat) : oddBit n = true <-> Odd n := by
  simp [oddBit]


theorem sources_boolCurrent_oddBit
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) :
    sources G (boolCurrent (fluxBitConfig G oddBit m)) =
      sources G (ofEdgeFun G m) := by
  ext v
  simp only [mem_sources]
  unfold incidentFlux boolCurrent fluxBitConfig
  let E := G.edgeFinset.filter (fun e => v ∈ e)
  have hfilter :
      E.filter (fun e => Odd
        (if (if h : e ∈ G.edgeFinset then oddBit (m ⟨e, h⟩) else false) = true
          then 1 else 0)) =
        E.filter (fun e => Odd (ofEdgeFun G m e)) := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨heE, heodd⟩
      refine ⟨heE, ?_⟩
      have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp heE).1
      by_cases ho : Odd (m ⟨e, heG⟩)
      · simpa [ofEdgeFun, heG] using ho
      · simp [heG, oddBit, ofEdgeFun, ho] at heodd
    · rintro ⟨heE, heodd⟩
      refine ⟨heE, ?_⟩
      have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp heE).1
      have ho : Odd (m ⟨e, heG⟩) := by
        simpa [heG, ofEdgeFun] using heodd
      simp [heG, oddBit, ofEdgeFun, ho]
  rw [Finset.odd_sum_iff_odd_card_odd,
    Finset.odd_sum_iff_odd_card_odd]
  apply iff_of_eq
  simpa only [E] using congrArg Odd (congrArg Finset.card hfilter)


end BackboneConcreteBondProgram
end
end StatMech.Sharpness
