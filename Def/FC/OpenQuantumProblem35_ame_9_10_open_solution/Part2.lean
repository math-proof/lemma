/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Instance.FC.OpenQuantumProblem35_ame_9_10_open_solution.Part2
open scoped BigOperators


namespace OpenQuantumProblem35

def q5Graph (i j : Fin 10) : ZMod 5 :=
  let e := Nat.dist i.1 j.1
  let e := min e (10 - e)
  if e = 1 then 3 else if e = 2 ∨ e = 3 then 1 else 0


def q5CutMatrix (A : Finset (Fin 10)) (hA : A.card = 5) :
    Matrix (Fin 5) (Fin 5) (ZMod 5) :=
  let hAc : Aᶜ.card = 5 := by simp [Finset.card_compl, hA]
  fun i j => q5Graph ((Aᶜ.orderIsoOfFin hAc) i).1 ((A.orderIsoOfFin hA) j).1


def q5Indices (mask : Fin 10 → Bool) (b : Bool) : List (Fin 10) :=
  (List.finRange 10).filter (fun i => mask i == b)

def q5Select (mask : Fin 10 → Bool) (b : Bool) (k : Fin 5) : ℕ :=
  ((q5Indices mask b)[k.1]?.getD 0).1

def q5GraphNat (i j : ℕ) : ℕ :=
  let e := Nat.dist i j
  let e := min e (10 - e)
  if e = 1 then 3 else if e = 2 ∨ e = 3 then 1 else 0

def q5MaskMatrix (mask : Fin 10 → Bool) : Matrix (Fin 5) (Fin 5) ℤ :=
  fun i j => q5GraphNat (q5Select mask false i) (q5Select mask true j)

set_option maxHeartbeats 0

set_option maxRecDepth 100000

def detFinThreeInt (M : Matrix (Fin 3) (Fin 3) ℤ) : ℤ :=
  M 0 0 * M 1 1 * M 2 2 + M 0 1 * M 1 2 * M 2 0 +
  M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0 -
  M 0 1 * M 1 0 * M 2 2 - M 0 0 * M 1 2 * M 2 1

def detFinFourInt (M : Matrix (Fin 4) (Fin 4) ℤ) : ℤ :=
  ∑ j : Fin 4, (-1) ^ (j : ℕ) * M 0 j *
    detFinThreeInt (M.submatrix (Fin.succAbove 0) (Fin.succAbove j))

def detFinFiveInt (M : Matrix (Fin 5) (Fin 5) ℤ) : ℤ :=
  ∑ j : Fin 5, (-1) ^ (j : ℕ) * M 0 j *
    detFinFourInt (M.submatrix (Fin.succAbove 0) (Fin.succAbove j))

def q5Affine (s : Fin 10) (flip : Bool) : Equiv.Perm (Fin 10) :=
  if flip then (Equiv.neg (Fin 10)).trans (Equiv.addLeft s) else Equiv.addLeft s


def q5Representatives : List (Finset (Fin 10)) :=
  [ {0, 1, 2, 3, 4}, {0, 1, 2, 3, 5}, {0, 1, 2, 4, 5},
    {0, 1, 2, 3, 6}, {0, 1, 2, 4, 6}, {0, 1, 3, 4, 6},
    {0, 2, 3, 4, 6}, {0, 1, 2, 5, 6}, {0, 1, 3, 5, 6},
    {0, 1, 2, 4, 7}, {0, 1, 3, 4, 7}, {0, 1, 2, 5, 7},
    {0, 1, 3, 5, 7}, {0, 2, 3, 5, 7}, {0, 1, 4, 5, 7},
    {0, 2, 4, 6, 8} ]

def finsetMapEquiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (S : Finset α) : S ≃ S.map e.toEmbedding where
  toFun x := ⟨e x, by simp⟩
  invFun y := ⟨e.symm y.1, by
    simpa only [Finset.mem_map_equiv] using y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

def finsetMapComplEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) (S : Finset α) :
    ↥(Sᶜ) ≃ ↥((S.map e.toEmbedding)ᶜ) where
  toFun x := ⟨e x.1, by
    simp only [Finset.mem_compl, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    simpa only [Finset.mem_compl] using x.2⟩
  invFun y := ⟨e.symm y.1, by
    simp only [Finset.mem_compl]
    have hy := y.2
    simpa only [Finset.mem_compl, Finset.mem_map_equiv] using hy⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp


def q2Cycle (i j : Fin 9) : ZMod 2 :=
  if Nat.dist i.1 j.1 = 1 ∨ Nat.dist i.1 j.1 = 8 then 1 else 0


def q2Check₁ (x : Fin 9 → ZMod 2) : ZMod 2 :=
  x 0 + x 1 + x 3 + x 4 + x 6 + x 7

def q2Check₂ (x : Fin 9 → ZMod 2) : ZMod 2 :=
  x 0 + x 2 + x 3 + x 5 + x 6 + x 8


def localTenEquiv : Fin 2 × Fin 5 ≃ Fin 10 := finProdFinEquiv

def bitPart (x : Fin 10) : ZMod 2 := (localTenEquiv.symm x).1

def quintPart (x : Fin 10) : ZMod 5 := (localTenEquiv.symm x).2


def localPartsEquiv : Fin 10 ≃ ZMod 2 × ZMod 5 :=
  localTenEquiv.symm.trans
    (Equiv.prodCongr (ZMod.finEquiv 2).toEquiv (ZMod.finEquiv 5).toEquiv)

end OpenQuantumProblem35
