/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawCollisionTokenEmbedding_of_weakComponentData
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (hcomponents : CanonicalStableRawWeakComponentTokenEmbeddingData
      ends m j k l zero hloop hjk hkl hk0 p hno) :
    CanonicalStableRawCollisionTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  let leftBase := canonicalStableRawSelfBase
    ends m j k l zero hloop hjk hkl hk0 p
  let rightBase := canonicalStableRawPreferredRightBase
    ends m j k l zero hloop hjk hkl hk0 p
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let L := StatMech.FrontierA.bipartiteLeftSurplusToken R T leftBase
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  change Nonempty
    (StatMech.FrontierA.bipartiteRightCollisionToken
      R T U rightBase ↪ L)
  change ∃ (leftComponent : L → Set E) (componentMap : Set E → E → L),
      _ at hcomponents
  obtain ⟨leftComponent, componentMap, htag, hinj⟩ := hcomponents
  let stateEmbedding : E ↪ L :=
    StatMech.FrontierA.embeddingOf_functionWeakComponentwiseMaps
      next leftComponent componentMap htag hinj
  let stateEquiv :=
    canonicalStableRawExceptionalEdgeEquivRightCollisionToken
      ends m j k l zero hloop hjk hkl hk0 p
  exact ⟨stateEquiv.symm.toEmbedding.trans stateEmbedding⟩

theorem canonicalStableRawExceptionalEdgeNext_target_ne
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    (canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s).target.1 ≠
        s.target.1 :=
  Classical.choose_spec (exists_canonicalStableRawExceptionalEdge_next
    ends m j k l zero hloop hjk hkl hk0 p hno s) |>.1


theorem canonicalStableRawExceptionalEdgeNext_square
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    let t := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s
    let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
    CanonicalRawGateRelated ends m j k l zero p
        s.source.1 t.target.1 ∧
      CanonicalRawGateRelated ends m j k l zero p b.1 t.target.1 ∧
      (t.source = s.source ∨ t.source = b) := by
  dsimp only
  have hs := Classical.choose_spec
    (exists_canonicalStableRawExceptionalEdge_next
      ends m j k l zero hloop hjk hkl hk0 p hno s)
  exact ⟨hs.2.1, hs.2.2.1, hs.2.2.2.1⟩


theorem canonicalStableRawExceptionalEdgeNext_source_or_owner_stable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    let t := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s
    let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
    t.source = b ∨
      (t.source = s.source ∧
        canonicalStableRawPreferredRightBase
          ends m j k l zero hloop hjk hkl hk0 p t.target = b.1) := by
  dsimp only
  exact (Classical.choose_spec
    (exists_canonicalStableRawExceptionalEdge_next
      ends m j k l zero hloop hjk hkl hk0 p hno s)).2.2.2.2


end StatMech.GrahamGHS.FourColor
