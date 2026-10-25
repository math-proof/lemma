/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeExhaustiveProgram
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeExhaustiveProgram

open BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackboneLabeledSwitching

open BackboneP2CoordinateReindex

open FluxEdgeCopy

theorem complete_implies_base
    (d : shb_ExplorationDomain V) (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat)
    (h : program.CompleteEvent d word m) :
    BackboneTwoEdgeBondProgram.program.CompleteEvent d word m := by
  unfold BondwiseSegmentProgram.CompleteEvent at h ⊢
  constructor
  · simpa [program, BackboneTwoEdgeBondProgram.program] using h.1
  · exact h.2.1


theorem program_complete_nil_iff
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    program.CompleteEvent d [] m <->
      sources d.graph (ofEdgeFun d.graph m) = ∅ := by
  constructor
  · exact fun h => (BackboneTwoEdgeBondProgram.program_complete_nil_iff d m).mp
      (complete_implies_base d [] m h)
  · intro hsource
    have hbase :=
      (BackboneTwoEdgeBondProgram.program_complete_nil_iff d m).mpr hsource
    unfold BondwiseSegmentProgram.CompleteEvent
      BondwiseSegmentProgram.TerminalEvent at hbase ⊢
    constructor
    · simpa [program, BackboneTwoEdgeBondProgram.program] using hbase.1
    · exact ⟨hbase.2, trivial⟩


theorem program_complete_singleton_iff_base
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (m : d.graph.edgeFinset -> Nat) :
    program.CompleteEvent d [s] m <->
      BackboneTwoEdgeBondProgram.program.CompleteEvent d [s] m := by
  constructor
  · exact complete_implies_base d [s] m
  · intro hbase
    unfold BondwiseSegmentProgram.CompleteEvent
      BondwiseSegmentProgram.TerminalEvent at hbase ⊢
    constructor
    · simpa [program, BackboneTwoEdgeBondProgram.program] using hbase.1
    · cases hedge : edgeOfSegment? d s <;>
        simpa [program, BackboneTwoEdgeBondProgram.program,
          BackboneTwoEdgeBondProgram.encode, hedge,
          BackboneTwoEdgeBondProgram.scan, terminal] using
          And.intro hbase.2 trivial


theorem program_complete_functional
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word word' : List (shb_ExplorationSegment V))
    (hword : program.CompleteEvent d word m)
    (hword' : program.CompleteEvent d word' m) : word = word' :=
  BackboneTwoEdgeBondProgram.program_complete_functional d m word word'
    (complete_implies_base d word m hword)
    (complete_implies_base d word' m hword')


theorem sources_eq_sourceClass_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) :
    sources d.graph (ofEdgeFun d.graph m) =
      BackboneTwoEdgeBondProgram.sourceClass d word :=
  BackboneTwoEdgeBondProgram.sources_eq_sourceClass_of_program_complete
    d m word (complete_implies_base d word m h)


theorem head_active_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V) (ss : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d (s :: ss) m) : s ∈ d.active :=
  BackboneTwoEdgeBondProgram.head_active_of_program_complete d m s ss
    (complete_implies_base d (s :: ss) m h)


end BackboneTwoEdgeExhaustiveProgram
end
end StatMech.Sharpness
