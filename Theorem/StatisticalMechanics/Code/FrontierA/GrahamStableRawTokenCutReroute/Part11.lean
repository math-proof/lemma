/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part10
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


@[simp] theorem mem_canonicalStableRawTokenComponent_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    s ∈ canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno s :=
  Relation.EqvGen.refl s

theorem canonicalStableRawTokenComponent_eq_of_mem
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    {s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p}
    (hst : t ∈ canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno s) :
    canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno t := by
  ext u
  constructor
  · intro hsu
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ hst) hsu
  · intro htu
    exact Relation.EqvGen.trans _ _ _ hst htu

@[simp] theorem canonicalStableRawTokenComponent_next
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno s) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  symm
  apply canonicalStableRawTokenComponent_eq_of_mem
  exact Relation.EqvGen.rel _ _ (Or.inl rfl)

@[simp] theorem canonicalStableRawTokenComponent_iterate
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) (n : Nat) :
    canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (canonicalStableRawTokenComponent_next
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)).trans ih

theorem canonicalStableRawTokenComponent_eq_of_target_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : s.target = t.target) :
    canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno t := by
  apply canonicalStableRawTokenComponent_eq_of_mem
  exact Relation.EqvGen.rel _ _ (Or.inr (Or.inl htarget))


theorem canonicalStableRawStateTokenIncidence_component_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hs : CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token s)
    (ht : CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token t) :
    canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno t := by
  apply canonicalStableRawTokenComponent_eq_of_mem
  exact Relation.EqvGen.rel _ _ (Or.inr (Or.inr ⟨token, hs, ht⟩))


end StatMech.GrahamGHS.FourColor
