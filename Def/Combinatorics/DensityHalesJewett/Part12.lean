/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DensityHalesJewett.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Combinatorics.HalesJewett
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Theorem.Combinatorics.DensityHalesJewett.Part10
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

def dhjBlockCore {k : ℕ} {J : Type*} (i : Fin k) {L : ℕ}
    (w : Fin L → J → Fin (k + 1)) : Fin L → J → Fin (k + 1) :=
  fun b => dhjReplaceLast i (w b)

def dhjBlockInsensitive {k : ℕ} {J : Type*} (i : Fin k) {L : ℕ}
    (D : Finset (Fin L → J → Fin (k + 1))) : Prop :=
  ∀ w, w ∈ D ↔ dhjBlockCore i w ∈ D

def dhjCurryEquiv {L : ℕ} {J α : Type*} :
    (Fin L → J → α) ≃ (Fin L × J → α) where
  toFun w q := w q.1 q.2
  invFun f b j := f (b, j)
  left_inv _ := rfl
  right_inv f := by
    funext q
    rcases q with ⟨b, j⟩
    rfl

def dhjMiddleWord {X : Type*} {Q t : ℕ} (h : t + 1 ≤ Q)
    (p : Fin t → X) (z : X) (y : Fin (Q - (t + 1)) → X) : Fin Q → X :=
  fun q =>
    if hqt : q.val < t then p ⟨q.val, hqt⟩
    else if hqeq : q.val = t then z
    else y ⟨q.val - (t + 1), by omega⟩

def dhjMiddleEquiv {X : Type*} {Q t : ℕ} (h : t + 1 ≤ Q) :
    (Fin Q → X) ≃
      (((Fin t → X) × (Fin (Q - (t + 1)) → X)) × X) where
  toFun w :=
    ((fun i => w ⟨i.val, by omega⟩,
      fun j => w ⟨t + 1 + j.val, by omega⟩),
      w ⟨t, by omega⟩)
  invFun q := dhjMiddleWord h q.1.1 q.2 q.1.2
  left_inv w := by
    funext q
    by_cases hqt : q.val < t
    · simp [dhjMiddleWord, hqt]
    · by_cases hqeq : q.val = t
      · subst hqeq
        simp [dhjMiddleWord]
      · simp only [dhjMiddleWord, hqt, hqeq, ↓reduceDIte]
        apply congrArg w
        apply Fin.ext
        simp
        omega
  right_inv q := by
    rcases q with ⟨⟨p, y⟩, z⟩
    apply Prod.ext
    · apply Prod.ext
      · funext i
        simp [dhjMiddleWord]
      · funext j
        simp only [dhjMiddleWord]
        have hnot : ¬ t + 1 + j.val < t := by omega
        have hne : t + 1 + j.val ≠ t := by omega
        simp [hnot, hne]
    · simp [dhjMiddleWord]

noncomputable def dhjMiddleSection {X : Type*} [Fintype X] {Q t : ℕ}
    (R : Finset (Fin Q → X)) (h : t + 1 ≤ Q)
    (b : (Fin t → X) × (Fin (Q - (t + 1)) → X)) : Finset X := by
  classical
  exact Finset.univ.filter fun z => dhjMiddleWord h b.1 z b.2 ∈ R

noncomputable def dhjProdSection {B X : Type*} [Fintype X]
    (A : Finset (B × X)) (b : B) : Finset X := by
  classical
  exact Finset.univ.filter fun x => (b, x) ∈ A

def dhjJoinAt {X : Type*} {Q t : ℕ} (h : t ≤ Q)
    (p : Fin t → X) (y : Fin (Q - t) → X) : Fin Q → X :=
  fun q => if hqt : q.val < t then p ⟨q.val, hqt⟩
    else y ⟨q.val - t, by omega⟩

def dhjTailCons {X : Type*} {Q t : ℕ} (h : t + 1 ≤ Q)
    (z : X) (y : Fin (Q - (t + 1)) → X) : Fin (Q - t) → X :=
  fun q => if hq : q.val = 0 then z else y ⟨q.val - 1, by omega⟩

def dhjStageInsensitive {k Q t : ℕ} {J : Type*} (i : Fin k)
    (R : Finset (Fin Q → J → Fin (k + 1))) (h : t ≤ Q) : Prop :=
  ∀ (p : Fin t → J → Fin (k + 1))
    (y y' : Fin (Q - t) → J → Fin (k + 1)),
    dhjBlockCore i y = dhjBlockCore i y' →
      (dhjJoinAt h p y ∈ R ↔ dhjJoinAt h p y' ∈ R)

def dhjBaseSuffixInsensitive {k Q t : ℕ} {J : Type*} (i : Fin k)
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1)))) : Prop :=
  ∀ (p : Fin t → J → Fin (k + 1))
    (y y' : Fin (Q - (t + 1)) → J → Fin (k + 1)),
    dhjBlockCore i y = dhjBlockCore i y' → ((p, y) ∈ S ↔ (p, y') ∈ S)

noncomputable def dhjBatch {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    Finset (Fin Q → J → Fin (k + 1)) := by
  classical
  exact (S.product (dhjSubspacePoints V)).map (dhjMiddleEquiv h).symm.toEmbedding

def dhjMiddleSubspace {k d Q t : ℕ} {J : Type*}
    (h : t + 1 ≤ Q)
    (b : (Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin Q × J) where
  idxFun q :=
    if hqt : q.1.val < t then Sum.inl (b.1 ⟨q.1.val, hqt⟩ q.2)
    else if hqeq : q.1.val = t then V.idxFun q.2
    else Sum.inl (b.2 ⟨q.1.val - (t + 1), by omega⟩ q.2)
  proper e := by
    obtain ⟨j, hj⟩ := V.proper e
    refine ⟨(⟨t, by omega⟩, j), ?_⟩
    simp [hj]

noncomputable def dhjFlatBatch {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    Finset (Fin Q × J → Fin (k + 1)) := by
  classical
  exact (dhjBatch h S V).map
    (dhjCurryEquiv (L := Q) (J := J) (α := Fin (k + 1))).toEmbedding

noncomputable def dhjFlatSet {k Q : ℕ} {J : Type*}
    (C : Finset (Fin Q → J → Fin (k + 1))) :
    Finset (Fin Q × J → Fin (k + 1)) := by
  classical
  exact C.map (dhjCurryEquiv (L := Q) (J := J) (α := Fin (k + 1))).toEmbedding

noncomputable def dhjTileGain (k d : ℕ) {J : Type*}
    [Fintype J] [Fintype (J → Fin (k + 1))] (β : ℝ) : ℝ :=
  β / Fintype.card (Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) *
    (((k + 1 : ℕ) : ℝ) ^ d / Fintype.card (J → Fin (k + 1)))

def dhjWordEquiv {I I' α : Type*} (e : I ≃ I') :
    (I → α) ≃ (I' → α) :=
  Equiv.arrowCongr e (Equiv.refl α)

end MathlibExt.Combinatorics.DensityHalesJewettWanted
