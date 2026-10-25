/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part22
open Finset


namespace StatMech.GrahamGHS.FourColor

universe u v uI uW

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


attribute [instance]
  FiniteRelationMinimalTightProblem.stateFintype
  FiniteRelationMinimalTightProblem.stateDecidableEq
  FiniteRelationMinimalTightProblem.tokenFintype
  FiniteRelationMinimalTightProblem.tokenDecidableEq

theorem canonicalStableRawStableCollisionTargetChildBlock_capacity
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (target : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hne : (canonicalStableRawStableCollisionTargetChildBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component target).Nonempty) :
    ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p),
      sources.card = (canonicalStableRawStableCollisionTargetChildBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component target).card ∧
      (canonicalStableRawStableCollisionTargetChildBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component target).card ≤
        (StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (sources.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
  classical
  let A := canonicalStableRawStableCollisionTargetChildBlock
    ends m j k l zero hloop hjk hkl hk0 p hno component target
  obtain ⟨x₀, hx₀⟩ := hne
  have hstable : ∀ x ∈ A, CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 := by
    intro x hx
    have hxData : CanonicalStableRawOwnerStableStep
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 ∧
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1).target =
          target := by
      simpa only [A, canonicalStableRawStableCollisionTargetChildBlock,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
    exact hxData.1
  have htarget : ∀ x ∈ A,
      (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1).target =
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1).target := by
    intro x hx
    have hxData : CanonicalStableRawOwnerStableStep
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 ∧
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1).target =
          target := by
      simpa only [A, canonicalStableRawStableCollisionTargetChildBlock,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
    have hx₀Data : CanonicalStableRawOwnerStableStep
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1 ∧
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1).target =
          target := by
      simpa only [A, canonicalStableRawStableCollisionTargetChildBlock,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx₀
    exact hxData.2.trans hx₀Data.2.symm
  obtain ⟨sources, _, hcard, hcapacity⟩ :=
    card_le_canonicalRawRelationNeighborhood_of_stableCollisionTargetBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ hx₀
        hstable htarget
  exact ⟨sources, hcard, hcapacity⟩


theorem canonicalStableRawAdvancingCollisionSuccessorChildBlock_capacity
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (successor : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hne : (canonicalStableRawAdvancingCollisionSuccessorChildBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component
        successor).Nonempty) :
    ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p),
      sources.card =
        (canonicalStableRawAdvancingCollisionSuccessorChildBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component
            successor).card ∧
      (canonicalStableRawAdvancingCollisionSuccessorChildBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component
            successor).card ≤
        (StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (sources.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
  classical
  let A := canonicalStableRawAdvancingCollisionSuccessorChildBlock
    ends m j k l zero hloop hjk hkl hk0 p hno component successor
  obtain ⟨x₀, hx₀⟩ := hne
  have hadvancing : ∀ x ∈ A, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 := by
    intro x hx
    have hxData : CanonicalStableRawOwnerAdvancingStep
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 ∧
        canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 =
          successor := by
      simpa only [A,
        canonicalStableRawAdvancingCollisionSuccessorChildBlock,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
    exact hxData.1
  have hnext : ∀ x ∈ A,
      canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 =
        canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1 := by
    intro x hx
    have hxData : CanonicalStableRawOwnerAdvancingStep
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 ∧
        canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 =
          successor := by
      simpa only [A,
        canonicalStableRawAdvancingCollisionSuccessorChildBlock,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
    have hx₀Data : CanonicalStableRawOwnerAdvancingStep
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1 ∧
        canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1 =
          successor := by
      simpa only [A,
        canonicalStableRawAdvancingCollisionSuccessorChildBlock,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx₀
    exact hxData.2.trans hx₀Data.2.symm
  obtain ⟨sources, _, hcard, hcapacity⟩ :=
    card_le_canonicalRawRelationNeighborhood_of_advancingCollisionBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ hx₀
        hadvancing hnext
  exact ⟨sources, hcard, hcapacity⟩


end StatMech.GrahamGHS.FourColor
