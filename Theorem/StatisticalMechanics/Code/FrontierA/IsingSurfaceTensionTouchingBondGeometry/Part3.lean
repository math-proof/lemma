/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismFaces.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry.Part3


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.Ising StatMech.IsingFK
  StatMech.Percolation


@[simp] theorem touchingBondKey_xInternal (n : Nat) (x : Fin (2 * n))
    (y z : Fin (2 * n + 1)) :
    touchingBondKey (oddPrismTouchIndexBond n (.xInternal x y z)) =
      ((2 * (x.val : Int) + 1 - 2 * n,
        2 * (y.val : Int) - 2 * n,
        2 * (n : Int) - 2 * z.val), (1, 0, 0)) := by
  simp [touchingBondKey, touchingBondCoordSum, touchingBondCoordDiff,
    oddPrismTouchIndexBond]
  ring_nf <;> simp

@[simp] theorem touchingBondKey_yInternal (n : Nat) (x : Fin (2 * n + 1))
    (y : Fin (2 * n)) (z : Fin (2 * n + 1)) :
    touchingBondKey (oddPrismTouchIndexBond n (.yInternal x y z)) =
      ((2 * (x.val : Int) - 2 * n,
        2 * (y.val : Int) + 1 - 2 * n,
        2 * (n : Int) - 2 * z.val), (0, 1, 0)) := by
  simp [touchingBondKey, touchingBondCoordSum, touchingBondCoordDiff,
    oddPrismTouchIndexBond]
  ring_nf <;> simp

@[simp] theorem touchingBondKey_zInternal (n : Nat)
    (x y : Fin (2 * n + 1)) (z : Fin (2 * n)) :
    touchingBondKey (oddPrismTouchIndexBond n (.zInternal x y z)) =
      ((2 * (x.val : Int) - 2 * n,
        2 * (y.val : Int) - 2 * n,
        2 * (n : Int) - 2 * z.val - 1), (0, 0, 1)) := by
  simp [touchingBondKey, touchingBondCoordSum, touchingBondCoordDiff,
    oddPrismTouchIndexBond]
  ring_nf <;> simp

@[simp] theorem touchingBondKey_xZero (n : Nat)
    (y z : Fin (2 * n + 1)) :
    touchingBondKey (oddPrismTouchIndexBond n (.xZero y z)) =
      ((-2 * (n : Int) - 1, 2 * (y.val : Int) - 2 * n,
        2 * (n : Int) - 2 * z.val), (1, 0, 0)) := by
  simp [touchingBondKey, touchingBondCoordSum, touchingBondCoordDiff,
    oddPrismTouchIndexBond, coordShift]
  ring_nf <;> simp

@[simp] theorem touchingBondKey_xLast (n : Nat)
    (y z : Fin (2 * n + 1)) :
    touchingBondKey (oddPrismTouchIndexBond n (.xLast y z)) =
      ((2 * (n : Int) + 1, 2 * (y.val : Int) - 2 * n,
        2 * (n : Int) - 2 * z.val), (1, 0, 0)) := by
  simp [touchingBondKey, touchingBondCoordSum, touchingBondCoordDiff,
    oddPrismTouchIndexBond, coordShift, Fin.last]
  ring_nf <;> simp

@[simp] theorem touchingBondKey_yZero (n : Nat)
    (x z : Fin (2 * n + 1)) :
    touchingBondKey (oddPrismTouchIndexBond n (.yZero x z)) =
      ((2 * (x.val : Int) - 2 * n, -2 * (n : Int) - 1,
        2 * (n : Int) - 2 * z.val), (0, 1, 0)) := by
  simp [touchingBondKey, touchingBondCoordSum, touchingBondCoordDiff,
    oddPrismTouchIndexBond, coordShift]
  ring_nf <;> simp

@[simp] theorem touchingBondKey_yLast (n : Nat)
    (x z : Fin (2 * n + 1)) :
    touchingBondKey (oddPrismTouchIndexBond n (.yLast x z)) =
      ((2 * (x.val : Int) - 2 * n, 2 * (n : Int) + 1,
        2 * (n : Int) - 2 * z.val), (0, 1, 0)) := by
  simp [touchingBondKey, touchingBondCoordSum, touchingBondCoordDiff,
    oddPrismTouchIndexBond, coordShift, Fin.last]
  ring_nf <;> simp

@[simp] theorem touchingBondKey_zZero (n : Nat)
    (x y : Fin (2 * n + 1)) :
    touchingBondKey (oddPrismTouchIndexBond n (.zZero x y)) =
      ((2 * (x.val : Int) - 2 * n, 2 * (y.val : Int) - 2 * n,
        2 * (n : Int) + 1), (0, 0, 1)) := by
  simp [touchingBondKey, touchingBondCoordSum, touchingBondCoordDiff,
    oddPrismTouchIndexBond, coordShift]
  ring_nf <;> simp

@[simp] theorem touchingBondKey_zLast (n : Nat)
    (x y : Fin (2 * n + 1)) :
    touchingBondKey (oddPrismTouchIndexBond n (.zLast x y)) =
      ((2 * (x.val : Int) - 2 * n, 2 * (y.val : Int) - 2 * n,
        -2 * (n : Int) - 1), (0, 0, 1)) := by
  simp [touchingBondKey, touchingBondCoordSum, touchingBondCoordDiff,
    oddPrismTouchIndexBond, coordShift, Fin.last]
  ring_nf <;> simp

set_option maxHeartbeats 2000000 in

theorem oddPrismTouchIndexBond_injective (n : Nat) :
    Function.Injective (oddPrismTouchIndexBond n) := by
  intro q r h
  have hk := congrArg touchingBondKey h
  clear h
  cases q <;> cases r <;>
    simp at hk ⊢ <;>
    congr <;> omega


theorem exists_oddPrism_xInternal_of_coordShift
    (n : Nat) {a b : Site 3} (ha : a ∈ box 3 n) (hb : b ∈ box 3 n)
    (hab : b = coordShift a 0 1) :
    ∃ q : OddPrismTouchIndex n,
      oddPrismTouchIndexBond n q = s(a, b) := by
  let e := rectangularPrismSiteEquivSctBoxDobrushin n
  let va := e.symm ⟨a, ha⟩
  let vb := e.symm ⟨b, hb⟩
  have hva : (e va).1 = a := by simp [va]
  have hvb : (e vb).1 = b := by simp [vb]
  have habv : (e vb).1 = coordShift (e va).1 0 1 := by
    rw [hva, hvb, hab]
  have h0 := congrArg (fun w : Site 3 => w 0) habv
  have h1 := congrArg (fun w : Site 3 => w 1) habv
  have h2 := congrArg (fun w : Site 3 => w 2) habv
  simp [e, coordShift] at h0 h1 h2
  have hxlt : va.x.val < 2 * n := by omega
  let x : Fin (2 * n) := ⟨va.x.val, hxlt⟩
  refine ⟨.xInternal x va.y va.z, ?_⟩
  rw [oddPrismTouchIndexBond]
  apply Sym2.eq_iff.mpr
  left
  constructor
  · rw [← hva]
  · rw [← hvb]
    congr 2
    rw [StatMech.Ising.RectangularPrismSite.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · apply Fin.ext
      dsimp [x]
      have hvxInt : (vb.x.val : Int) = (va.x.val : Int) + 1 := by
        linarith
      exact_mod_cast hvxInt.symm
    · apply Fin.ext
      exact h1.symm
    · apply Fin.ext
      exact h2.symm

theorem exists_oddPrism_yInternal_of_coordShift
    (n : Nat) {a b : Site 3} (ha : a ∈ box 3 n) (hb : b ∈ box 3 n)
    (hab : b = coordShift a 1 1) :
    ∃ q : OddPrismTouchIndex n,
      oddPrismTouchIndexBond n q = s(a, b) := by
  let e := rectangularPrismSiteEquivSctBoxDobrushin n
  let va := e.symm ⟨a, ha⟩
  let vb := e.symm ⟨b, hb⟩
  have hva : (e va).1 = a := by simp [va]
  have hvb : (e vb).1 = b := by simp [vb]
  have habv : (e vb).1 = coordShift (e va).1 1 1 := by
    rw [hva, hvb, hab]
  have h0 := congrArg (fun w : Site 3 => w 0) habv
  have h1 := congrArg (fun w : Site 3 => w 1) habv
  have h2 := congrArg (fun w : Site 3 => w 2) habv
  simp [e, coordShift] at h0 h1 h2
  have hylt : va.y.val < 2 * n := by omega
  let y : Fin (2 * n) := ⟨va.y.val, hylt⟩
  refine ⟨.yInternal va.x y va.z, ?_⟩
  rw [oddPrismTouchIndexBond]
  apply Sym2.eq_iff.mpr
  left
  constructor
  · rw [← hva]
  · rw [← hvb]
    congr 2
    rw [StatMech.Ising.RectangularPrismSite.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · apply Fin.ext
      exact h0.symm
    · apply Fin.ext
      dsimp [y]
      have hvyInt : (vb.y.val : Int) = (va.y.val : Int) + 1 := by
        linarith
      exact_mod_cast hvyInt.symm
    · apply Fin.ext
      exact h2.symm

theorem exists_oddPrism_zInternal_of_coordShift
    (n : Nat) {a b : Site 3} (ha : a ∈ box 3 n) (hb : b ∈ box 3 n)
    (hab : b = coordShift a 2 1) :
    ∃ q : OddPrismTouchIndex n,
      oddPrismTouchIndexBond n q = s(a, b) := by
  let e := rectangularPrismSiteEquivSctBoxDobrushin n
  let va := e.symm ⟨a, ha⟩
  let vb := e.symm ⟨b, hb⟩
  have hva : (e va).1 = a := by simp [va]
  have hvb : (e vb).1 = b := by simp [vb]
  have habv : (e vb).1 = coordShift (e va).1 2 1 := by
    rw [hva, hvb, hab]
  have h0 := congrArg (fun w : Site 3 => w 0) habv
  have h1 := congrArg (fun w : Site 3 => w 1) habv
  have h2 := congrArg (fun w : Site 3 => w 2) habv
  simp [e, coordShift] at h0 h1 h2
  have hzlt : vb.z.val < 2 * n := by omega
  let z : Fin (2 * n) := ⟨vb.z.val, hzlt⟩
  refine ⟨.zInternal vb.x vb.y z, ?_⟩
  rw [oddPrismTouchIndexBond]
  apply Sym2.eq_iff.mpr
  right
  constructor
  · rw [← hvb]
  · rw [← hva]
    congr 2
    rw [StatMech.Ising.RectangularPrismSite.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · apply Fin.ext
      exact h0
    · apply Fin.ext
      exact h1
    · apply Fin.ext
      dsimp [z]
      have hvzInt : (va.z.val : Int) = (vb.z.val : Int) + 1 := by
        linarith
      exact_mod_cast hvzInt.symm

@[simp] theorem coordShift_neg_one_then_one
    (x : Site 3) (i : Fin 3) :
    coordShift (coordShift x i (-1)) i 1 = x := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [coordShift]
  · simp [coordShift, Function.update_of_ne hji]


theorem exists_oddPrism_internal_of_adj
    (n : Nat) {a b : Site 3} (ha : a ∈ box 3 n) (hb : b ∈ box 3 n)
    (hadj : (hypercubicLattice 3).Adj a b) :
    ∃ q : OddPrismTouchIndex n,
      oddPrismTouchIndexBond n q = s(a, b) := by
  obtain ⟨i, sign, hab⟩ := adj_exists_dir hadj
  fin_cases i <;> cases sign
  · have hba : b = coordShift a 0 (-1) := by simpa [stepSign] using hab
    have hrev : a = coordShift b 0 1 := by
      rw [hba, coordShift_neg_one_then_one]
    obtain ⟨q, hq⟩ := exists_oddPrism_xInternal_of_coordShift n hb ha hrev
    exact ⟨q, hq.trans Sym2.eq_swap⟩
  · exact exists_oddPrism_xInternal_of_coordShift n ha hb (by simpa [stepSign] using hab)
  · have hba : b = coordShift a 1 (-1) := by simpa [stepSign] using hab
    have hrev : a = coordShift b 1 1 := by
      rw [hba, coordShift_neg_one_then_one]
    obtain ⟨q, hq⟩ := exists_oddPrism_yInternal_of_coordShift n hb ha hrev
    exact ⟨q, hq.trans Sym2.eq_swap⟩
  · exact exists_oddPrism_yInternal_of_coordShift n ha hb (by simpa [stepSign] using hab)
  · have hba : b = coordShift a 2 (-1) := by simpa [stepSign] using hab
    have hrev : a = coordShift b 2 1 := by
      rw [hba, coordShift_neg_one_then_one]
    obtain ⟨q, hq⟩ := exists_oddPrism_zInternal_of_coordShift n hb ha hrev
    exact ⟨q, hq.trans Sym2.eq_swap⟩
  · exact exists_oddPrism_zInternal_of_coordShift n ha hb (by simpa [stepSign] using hab)


theorem exists_oddPrism_xZero_of_coordShift
    (n : Nat) {a b : Site 3} (ha : a ∈ box 3 n) (hb : b ∉ box 3 n)
    (hab : b = coordShift a 0 (-1)) :
    ∃ q : OddPrismTouchIndex n,
      oddPrismTouchIndexBond n q = s(a, b) := by
  let e := rectangularPrismSiteEquivSctBoxDobrushin n
  let va := e.symm ⟨a, ha⟩
  have hva : (e va).1 = a := by simp [va]
  have ha0 : a 0 = (va.x.val : Int) - n := by
    rw [← hva]
    simp [e]
  have hvx0 : va.x.val = 0 := by
    by_contra hvx0
    apply hb
    intro j
    fin_cases j
    · rw [hab]
      simp [coordShift]
      have hbound := ha 0
      omega
    · simpa [hab, coordShift] using ha 1
    · simpa [hab, coordShift] using ha 2
  refine ⟨.xZero va.y va.z, ?_⟩
  have hface : (e ⟨0, va.y, va.z⟩).1 = a := by
    rw [← hva]
    congr 2
    rw [StatMech.Ising.RectangularPrismSite.mk.injEq]
    refine ⟨?_, rfl, rfl⟩
    apply Fin.ext
    simpa using hvx0.symm
  change s((e ⟨0, va.y, va.z⟩).1,
      coordShift (e ⟨0, va.y, va.z⟩).1 0 (-1)) = s(a, b)
  rw [hface, hab]

theorem exists_oddPrism_xLast_of_coordShift
    (n : Nat) {a b : Site 3} (ha : a ∈ box 3 n) (hb : b ∉ box 3 n)
    (hab : b = coordShift a 0 1) :
    ∃ q : OddPrismTouchIndex n,
      oddPrismTouchIndexBond n q = s(a, b) := by
  let e := rectangularPrismSiteEquivSctBoxDobrushin n
  let va := e.symm ⟨a, ha⟩
  have hva : (e va).1 = a := by simp [va]
  have ha0 : a 0 = (va.x.val : Int) - n := by rw [← hva]; simp [e]
  have hvxLast : va.x.val = 2 * n := by
    by_contra hvxLast
    apply hb
    intro j
    fin_cases j
    · rw [hab]
      simp [coordShift]
      have hbound := ha 0
      omega
    · simpa [hab, coordShift] using ha 1
    · simpa [hab, coordShift] using ha 2
  refine ⟨.xLast va.y va.z, ?_⟩
  have hface : (e ⟨Fin.last (2 * n), va.y, va.z⟩).1 = a := by
    rw [← hva]
    congr 2
    rw [StatMech.Ising.RectangularPrismSite.mk.injEq]
    refine ⟨?_, rfl, rfl⟩
    apply Fin.ext
    simpa using hvxLast.symm
  change s((e ⟨Fin.last (2 * n), va.y, va.z⟩).1,
      coordShift (e ⟨Fin.last (2 * n), va.y, va.z⟩).1 0 1) = s(a, b)
  rw [hface, hab]

theorem exists_oddPrism_yZero_of_coordShift
    (n : Nat) {a b : Site 3} (ha : a ∈ box 3 n) (hb : b ∉ box 3 n)
    (hab : b = coordShift a 1 (-1)) :
    ∃ q : OddPrismTouchIndex n,
      oddPrismTouchIndexBond n q = s(a, b) := by
  let e := rectangularPrismSiteEquivSctBoxDobrushin n
  let va := e.symm ⟨a, ha⟩
  have hva : (e va).1 = a := by simp [va]
  have ha1 : a 1 = (va.y.val : Int) - n := by rw [← hva]; simp [e]
  have hvy0 : va.y.val = 0 := by
    by_contra hvy0
    apply hb
    intro j
    fin_cases j
    · simpa [hab, coordShift] using ha 0
    · rw [hab]
      simp [coordShift]
      have hbound := ha 1
      omega
    · simpa [hab, coordShift] using ha 2
  refine ⟨.yZero va.x va.z, ?_⟩
  have hface : (e ⟨va.x, 0, va.z⟩).1 = a := by
    rw [← hva]
    congr 2
    rw [StatMech.Ising.RectangularPrismSite.mk.injEq]
    refine ⟨rfl, ?_, rfl⟩
    apply Fin.ext
    simpa using hvy0.symm
  change s((e ⟨va.x, 0, va.z⟩).1,
      coordShift (e ⟨va.x, 0, va.z⟩).1 1 (-1)) = s(a, b)
  rw [hface, hab]

theorem exists_oddPrism_yLast_of_coordShift
    (n : Nat) {a b : Site 3} (ha : a ∈ box 3 n) (hb : b ∉ box 3 n)
    (hab : b = coordShift a 1 1) :
    ∃ q : OddPrismTouchIndex n,
      oddPrismTouchIndexBond n q = s(a, b) := by
  let e := rectangularPrismSiteEquivSctBoxDobrushin n
  let va := e.symm ⟨a, ha⟩
  have hva : (e va).1 = a := by simp [va]
  have ha1 : a 1 = (va.y.val : Int) - n := by rw [← hva]; simp [e]
  have hvyLast : va.y.val = 2 * n := by
    by_contra hvyLast
    apply hb
    intro j
    fin_cases j
    · simpa [hab, coordShift] using ha 0
    · rw [hab]
      simp [coordShift]
      have hbound := ha 1
      omega
    · simpa [hab, coordShift] using ha 2
  refine ⟨.yLast va.x va.z, ?_⟩
  have hface : (e ⟨va.x, Fin.last (2 * n), va.z⟩).1 = a := by
    rw [← hva]
    congr 2
    rw [StatMech.Ising.RectangularPrismSite.mk.injEq]
    refine ⟨rfl, ?_, rfl⟩
    apply Fin.ext
    simpa using hvyLast.symm
  change s((e ⟨va.x, Fin.last (2 * n), va.z⟩).1,
      coordShift (e ⟨va.x, Fin.last (2 * n), va.z⟩).1 1 1) = s(a, b)
  rw [hface, hab]

theorem exists_oddPrism_zZero_of_coordShift
    (n : Nat) {a b : Site 3} (ha : a ∈ box 3 n) (hb : b ∉ box 3 n)
    (hab : b = coordShift a 2 1) :
    ∃ q : OddPrismTouchIndex n,
      oddPrismTouchIndexBond n q = s(a, b) := by
  let e := rectangularPrismSiteEquivSctBoxDobrushin n
  let va := e.symm ⟨a, ha⟩
  have hva : (e va).1 = a := by simp [va]
  have ha2 : a 2 = (n : Int) - va.z.val := by rw [← hva]; simp [e]
  have hvz0 : va.z.val = 0 := by
    by_contra hvz0
    apply hb
    intro j
    fin_cases j
    · simpa [hab, coordShift] using ha 0
    · simpa [hab, coordShift] using ha 1
    · rw [hab]
      simp [coordShift]
      have hbound := ha 2
      omega
  refine ⟨.zZero va.x va.y, ?_⟩
  have hface : (e ⟨va.x, va.y, 0⟩).1 = a := by
    rw [← hva]
    congr 2
    rw [StatMech.Ising.RectangularPrismSite.mk.injEq]
    refine ⟨rfl, rfl, ?_⟩
    apply Fin.ext
    simpa using hvz0.symm
  change s((e ⟨va.x, va.y, 0⟩).1,
      coordShift (e ⟨va.x, va.y, 0⟩).1 2 1) = s(a, b)
  rw [hface, hab]

theorem exists_oddPrism_zLast_of_coordShift
    (n : Nat) {a b : Site 3} (ha : a ∈ box 3 n) (hb : b ∉ box 3 n)
    (hab : b = coordShift a 2 (-1)) :
    ∃ q : OddPrismTouchIndex n,
      oddPrismTouchIndexBond n q = s(a, b) := by
  let e := rectangularPrismSiteEquivSctBoxDobrushin n
  let va := e.symm ⟨a, ha⟩
  have hva : (e va).1 = a := by simp [va]
  have ha2 : a 2 = (n : Int) - va.z.val := by rw [← hva]; simp [e]
  have hvzLast : va.z.val = 2 * n := by
    by_contra hvzLast
    apply hb
    intro j
    fin_cases j
    · simpa [hab, coordShift] using ha 0
    · simpa [hab, coordShift] using ha 1
    · rw [hab]
      simp [coordShift]
      have hbound := ha 2
      omega
  refine ⟨.zLast va.x va.y, ?_⟩
  have hface : (e ⟨va.x, va.y, Fin.last (2 * n)⟩).1 = a := by
    rw [← hva]
    congr 2
    rw [StatMech.Ising.RectangularPrismSite.mk.injEq]
    refine ⟨rfl, rfl, ?_⟩
    apply Fin.ext
    simpa using hvzLast.symm
  change s((e ⟨va.x, va.y, Fin.last (2 * n)⟩).1,
      coordShift (e ⟨va.x, va.y, Fin.last (2 * n)⟩).1 2 (-1)) = s(a, b)
  rw [hface, hab]


theorem exists_oddPrism_boundary_of_adj
    (n : Nat) {a b : Site 3} (ha : a ∈ box 3 n) (hb : b ∉ box 3 n)
    (hadj : (hypercubicLattice 3).Adj a b) :
    ∃ q : OddPrismTouchIndex n,
      oddPrismTouchIndexBond n q = s(a, b) := by
  obtain ⟨i, sign, hab⟩ := adj_exists_dir hadj
  fin_cases i <;> cases sign
  · exact exists_oddPrism_xZero_of_coordShift n ha hb
      (by simpa [stepSign] using hab)
  · exact exists_oddPrism_xLast_of_coordShift n ha hb
      (by simpa [stepSign] using hab)
  · exact exists_oddPrism_yZero_of_coordShift n ha hb
      (by simpa [stepSign] using hab)
  · exact exists_oddPrism_yLast_of_coordShift n ha hb
      (by simpa [stepSign] using hab)
  · exact exists_oddPrism_zLast_of_coordShift n ha hb
      (by simpa [stepSign] using hab)
  · exact exists_oddPrism_zZero_of_coordShift n ha hb
      (by simpa [stepSign] using hab)


theorem oddPrismTouchIndexBond_surjective (n : Nat) :
    Function.Surjective (fun q : OddPrismTouchIndex n =>
      (⟨oddPrismTouchIndexBond n q,
        oddPrismTouchIndexBond_mem n q⟩ :
          {e // e ∈ bondFinsetTouch 3 n})) := by
  rintro ⟨edge, hedge⟩
  induction edge using Sym2.ind with
  | _ a b =>
      rw [hbx_mem_bondFinsetTouch_iff] at hedge
      rcases hedge with ⟨hadj, htouch⟩
      by_cases ha : a ∈ box 3 n
      · by_cases hb : b ∈ box 3 n
        · obtain ⟨q, hq⟩ := exists_oddPrism_internal_of_adj n ha hb hadj
          refine ⟨q, Subtype.ext ?_⟩
          exact hq
        · obtain ⟨q, hq⟩ := exists_oddPrism_boundary_of_adj n ha hb hadj
          refine ⟨q, Subtype.ext ?_⟩
          exact hq
      · have hb : b ∈ box 3 n := htouch.resolve_left ha
        obtain ⟨q, hq⟩ := exists_oddPrism_boundary_of_adj n hb ha hadj.symm
        refine ⟨q, Subtype.ext ?_⟩
        exact hq.trans Sym2.eq_swap


end StatMech.FrontierA
