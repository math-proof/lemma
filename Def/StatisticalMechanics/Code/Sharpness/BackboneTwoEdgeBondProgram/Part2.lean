/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeBondProgram

open BackboneConcreteSelector

open BackboneConcreteBondProgram

open BackboneDeterminedCutSwitching

noncomputable def canonicalPairPath
    (G : SimpleGraph V) (e f : G.edgeFinset)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment G e)
      (canonicalEdgeSegment G f)) :
    (⊤ : SimpleGraph V).Path (canonicalEdgeSegment G e).1
      (canonicalEdgeSegment G f).2.1 := by
  change (⊤ : SimpleGraph V).Path e.1.out.1 f.1.out.2
  have hjoin : e.1.out.2 = f.1.out.1 := hpath.1
  have houter : e.1.out.1 ≠ f.1.out.2 := hpath.2
  have hab : e.1.out.1 ≠ e.1.out.2 := by
    simpa only [canonicalEdgeSegment] using
      canonicalEdgeSegment_start_ne_end G e
  have hfc : f.1.out.1 ≠ f.1.out.2 := by
    simpa only [canonicalEdgeSegment] using
      canonicalEdgeSegment_start_ne_end G f
  have hbc : e.1.out.2 ≠ f.1.out.2 := by
    rw [hjoin]
    exact hfc
  let w : (⊤ : SimpleGraph V).Walk e.1.out.1 f.1.out.2 :=
    SimpleGraph.Walk.cons (by simpa using hab)
      (SimpleGraph.Walk.cons (by simpa using hbc)
        SimpleGraph.Walk.nil)
  refine ⟨w, ?_⟩
  simp [w, hab, hbc, houter]


end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
