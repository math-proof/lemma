/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Def.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwLocalAngularSplitBlocks_internal_apply_of_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G (data.order))
    (hstep : KWOrderedInternalDartStep G
      (data.order) d e) :
    (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ d e = 1 :=
  kwLocalAngularSplit_internalBlock_apply_of_step data weight d e hstep

theorem kwLocalAngularSplitBlocks_internal_apply_of_not_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G (data.order))
    (hstep : ¬KWOrderedInternalDartStep G
      (data.order) d e) :
    (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ d e = 0 :=
  kwLocalAngularSplit_internalBlock_apply_of_not_step data weight d e hstep

theorem kwLocalAngularSplitBlocks_enter_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (data.order))
    (hconnect : kwPortOfDart G d.symm = e.1.fst) :
    (kwLocalAngularSplitBlocks data weight).toBlocks₁₂ d e =
      weight d.edge * kwLocalAngularSplitPhase data
        (kwOrderedExternalSplitDartOfDart G
          (data.order) d).1 e.1 :=
  kwLocalAngularSplit_enterBlock_apply_of_connect
    data weight d e hconnect

theorem kwLocalAngularSplitBlocks_enter_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (data.order))
    (hconnect : kwPortOfDart G d.symm ≠ e.1.fst) :
    (kwLocalAngularSplitBlocks data weight).toBlocks₁₂ d e = 0 :=
  kwLocalAngularSplit_enterBlock_apply_of_not_connect
    data weight d e hconnect

theorem kwLocalAngularSplitBlocks_exit_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (data.order))
    (e : G.Dart) (hconnect : d.1.snd = kwPortOfDart G e) :
    (kwLocalAngularSplitBlocks data weight).toBlocks₂₁ d e =
      data.root (kwPortOfDart G e) :=
  kwLocalAngularSplit_exitBlock_apply_of_connect
    data weight d e hconnect

theorem kwLocalAngularSplitBlocks_exit_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (data.order))
    (e : G.Dart) (hconnect : d.1.snd ≠ kwPortOfDart G e) :
    (kwLocalAngularSplitBlocks data weight).toBlocks₂₁ d e = 0 :=
  kwLocalAngularSplit_exitBlock_apply_of_not_connect
    data weight d e hconnect


end StatMech.FrontierA
