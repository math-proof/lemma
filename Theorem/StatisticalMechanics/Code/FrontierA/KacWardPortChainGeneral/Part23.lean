/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part23
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwAngularSplitBlocks_internal_apply_of_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hstep : KWOrderedInternalDartStep G
      (kwAngularPortOrder embedding) d e) :
    (kwAngularSplitBlocks embedding weight).toBlocks₂₂ d e = 1 :=
  kwAngularSplit_internalBlock_apply_of_step embedding weight d e hstep

theorem kwAngularSplitBlocks_internal_apply_of_not_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hstep : ¬KWOrderedInternalDartStep G
      (kwAngularPortOrder embedding) d e) :
    (kwAngularSplitBlocks embedding weight).toBlocks₂₂ d e = 0 :=
  kwAngularSplit_internalBlock_apply_of_not_step embedding weight d e hstep

theorem kwAngularSplitBlocks_enter_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hconnect : kwPortOfDart G d.symm = e.1.fst) :
    (kwAngularSplitBlocks embedding weight).toBlocks₁₂ d e =
      weight d.edge * kwAngularSplitPhase embedding
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) d).1 e.1 :=
  kwAngularSplit_enterBlock_apply_of_connect
    embedding weight d e hconnect

theorem kwAngularSplitBlocks_enter_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hconnect : kwPortOfDart G d.symm ≠ e.1.fst) :
    (kwAngularSplitBlocks embedding weight).toBlocks₁₂ d e = 0 :=
  kwAngularSplit_enterBlock_apply_of_not_connect
    embedding weight d e hconnect

theorem kwAngularSplitBlocks_exit_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart) (hconnect : d.1.snd = kwPortOfDart G e) :
    (kwAngularSplitBlocks embedding weight).toBlocks₂₁ d e =
      kwPortAngleRoot embedding (kwPortOfDart G e) :=
  kwAngularSplit_exitBlock_apply_of_connect
    embedding weight d e hconnect

theorem kwAngularSplitBlocks_exit_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart) (hconnect : d.1.snd ≠ kwPortOfDart G e) :
    (kwAngularSplitBlocks embedding weight).toBlocks₂₁ d e = 0 :=
  kwAngularSplit_exitBlock_apply_of_not_connect
    embedding weight d e hconnect


end StatMech.FrontierA
