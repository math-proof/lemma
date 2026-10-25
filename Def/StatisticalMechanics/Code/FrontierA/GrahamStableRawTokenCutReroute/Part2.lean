/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalStableRawExceptionalEdgeNext
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p) :
    CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p →
      CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p := fun s =>
  Classical.choose (exists_canonicalStableRawExceptionalEdge_next
    ends m j k l zero hloop hjk hkl hk0 p hno s)


noncomputable def CanonicalStableRawWeakComponentTokenEmbeddingData
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p) : Prop := by
  classical
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let leftBase := canonicalStableRawSelfBase
    ends m j k l zero hloop hjk hkl hk0 p
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let L := StatMech.FrontierA.bipartiteLeftSurplusToken R T leftBase
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  exact ∃ (leftComponent : L → Set E) (componentMap : Set E → E → L),
    (∀ component s,
      StatMech.FrontierA.functionWeakComponent next s = component ->
        leftComponent (componentMap component s) = component) ∧
    ∀ component, Function.Injective fun
      s : {s : E //
        StatMech.FrontierA.functionWeakComponent next s = component} =>
      componentMap component s.1


end StatMech.GrahamGHS.FourColor
