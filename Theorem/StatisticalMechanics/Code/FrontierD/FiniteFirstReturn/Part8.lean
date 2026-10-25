/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8


namespace StatMech.FrontierD

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

@[simp] theorem finiteFirstReturnOccurrencePoint_zero
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (i : Fin states.length) :
    finiteFirstReturnOccurrencePoint sigma selected states
        (finiteFirstReturnOccurrenceIndexZero sigma selected states i) =
      (states.get i).1 := by
  simp [finiteFirstReturnOccurrencePoint,
    finiteFirstReturnOccurrenceIndexZero]

section Related

variable {B : Type*} [Fintype B] [DecidableEq B]


theorem finiteRelated_until_firstReturn
    (sigma : Equiv.Perm A) (tau : Equiv.Perm B)
    (selectedA : A -> Prop) (selectedB : B -> Prop)
    [DecidablePred selectedA] [DecidablePred selectedB]
    (R : A -> B -> Prop)
    (hstep : forall {a b}, R a b -> Not (selectedA a) ->
      Not (selectedB b) -> R (sigma a) (tau b))
    (x : {a : A // selectedA a}) (y : {b : B // selectedB b})
    (hfirst : R (sigma x.1) (tau y.1))
    (n : Nat) (hnpos : 0 < n)
    (hnA : n <= finiteFirstReturnTime sigma selectedA x)
    (hnB : n <= finiteFirstReturnTime tau selectedB y) :
    R ((sigma ^ n) x.1) ((tau ^ n) y.1) := by
  induction n using Nat.case_strong_induction_on with
  | hz => exact False.elim (by omega)
  | hi n ih =>
      by_cases hnzero : n = 0
      · subst n
        simpa [Equiv.Perm.mul_apply] using hfirst
      · have hnpos' : 0 < n := Nat.pos_of_ne_zero hnzero
        have hnA' : n <= finiteFirstReturnTime sigma selectedA x := by omega
        have hnB' : n <= finiteFirstReturnTime tau selectedB y := by omega
        have hrel := ih n (by omega) hnpos' hnA' hnB'
        have hnAlt : n < finiteFirstReturnTime sigma selectedA x := by omega
        have hnBlt : n < finiteFirstReturnTime tau selectedB y := by omega
        have hnotA : Not (selectedA ((sigma ^ n) x.1)) := by
          intro hs
          exact (finiteFirstReturnTime_minimal sigma selectedA x n hnAlt)
            ⟨hnpos', hs⟩
        have hnotB : Not (selectedB ((tau ^ n) y.1)) := by
          intro hs
          exact (finiteFirstReturnTime_minimal tau selectedB y n hnBlt)
            ⟨hnpos', hs⟩
        simpa [pow_succ', Equiv.Perm.mul_apply] using
          hstep hrel hnotA hnotB

theorem finiteFirstReturnTime_eq_of_aligned_first
    (sigma : Equiv.Perm A) (tau : Equiv.Perm B)
    (selectedA : A -> Prop) (selectedB : B -> Prop)
    [DecidablePred selectedA] [DecidablePred selectedB]
    (R : A -> B -> Prop)
    (hselected : forall {a b}, R a b ->
      (selectedA a <-> selectedB b))
    (hstep : forall {a b}, R a b -> Not (selectedA a) ->
      Not (selectedB b) -> R (sigma a) (tau b))
    (x : {a : A // selectedA a}) (y : {b : B // selectedB b})
    (hfirst : R (sigma x.1) (tau y.1)) :
    finiteFirstReturnTime sigma selectedA x =
      finiteFirstReturnTime tau selectedB y := by
  let m := finiteFirstReturnTime sigma selectedA x
  let n := finiteFirstReturnTime tau selectedB y
  rcases le_total m n with hmn | hnm
  · have hrel := finiteRelated_until_firstReturn sigma tau
      selectedA selectedB R hstep x y hfirst m
      (finiteFirstReturnTime_pos sigma selectedA x) (by rfl) hmn
    have hselectedB : selectedB ((tau ^ m) y.1) :=
      (hselected hrel).mp
        (finiteFirstReturnTime_selected sigma selectedA x)
    have hnm' : n <= m := Nat.find_min'
      (finiteReturnWitness tau selectedB y)
      ⟨finiteFirstReturnTime_pos sigma selectedA x, hselectedB⟩
    exact Nat.le_antisymm hmn hnm'
  · have hrel := finiteRelated_until_firstReturn sigma tau
      selectedA selectedB R hstep x y hfirst n
      (finiteFirstReturnTime_pos tau selectedB y) hnm (by rfl)
    have hselectedA : selectedA ((sigma ^ n) x.1) :=
      (hselected hrel).mpr
        (finiteFirstReturnTime_selected tau selectedB y)
    have hmn' : m <= n := Nat.find_min'
      (finiteReturnWitness sigma selectedA x)
      ⟨finiteFirstReturnTime_pos tau selectedB y, hselectedA⟩
    exact Nat.le_antisymm hmn' hnm

theorem finiteFirstReturn_related_of_aligned_first
    (sigma : Equiv.Perm A) (tau : Equiv.Perm B)
    (selectedA : A -> Prop) (selectedB : B -> Prop)
    [DecidablePred selectedA] [DecidablePred selectedB]
    (R : A -> B -> Prop)
    (hselected : forall {a b}, R a b ->
      (selectedA a <-> selectedB b))
    (hstep : forall {a b}, R a b -> Not (selectedA a) ->
      Not (selectedB b) -> R (sigma a) (tau b))
    (x : {a : A // selectedA a}) (y : {b : B // selectedB b})
    (hfirst : R (sigma x.1) (tau y.1)) :
    R (finiteFirstReturn sigma selectedA x).1
      (finiteFirstReturn tau selectedB y).1 := by
  let htime := finiteFirstReturnTime_eq_of_aligned_first sigma tau
    selectedA selectedB R hselected hstep x y hfirst
  unfold finiteFirstReturn
  change R ((sigma ^ finiteFirstReturnTime sigma selectedA x) x.1)
    ((tau ^ finiteFirstReturnTime tau selectedB y) y.1)
  rw [← htime]
  apply finiteRelated_until_firstReturn sigma tau selectedA selectedB
    R hstep x y hfirst
  · exact finiteFirstReturnTime_pos sigma selectedA x
  · rfl
  · rw [htime]

end Related
end
end StatMech.FrontierD
