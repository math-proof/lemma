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
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace Combinatorics.Line

variable {α ι ι' : Type*}

/-- Reindex the coordinates of a combinatorial line along an equivalence. -/
def reindex (l : Line α ι) (e : ι ≃ ι') : Line α ι' where
  idxFun i := l.idxFun (e.symm i)
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨e i, by simpa⟩

end Combinatorics.Line

namespace Combinatorics.Subspace

/-- Compose a combinatorial subspace with a combinatorial subspace inside it. -/
def comp (V : Subspace η α ι) (W : Subspace η' α η) : Subspace η' α ι where
  idxFun i := (V.idxFun i).elim Sum.inl W.idxFun
  proper e := by
    obtain ⟨j, hj⟩ := W.proper e
    obtain ⟨i, hi⟩ := V.proper j
    exact ⟨i, by simp [hi, hj]⟩

/-- Transport a combinatorial line through a combinatorial subspace. -/
def compLine (V : Subspace η α ι) (l : Combinatorics.Line α η) :
    Combinatorics.Line α ι where
  idxFun i := (V.idxFun i).elim some l.idxFun
  proper := by
    obtain ⟨e, he⟩ := l.proper
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨i, by simp [hi, he]⟩

end Combinatorics.Subspace

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

def dhjDistinguishedLine {η α : Type*} (x : η → Option α) :
    Combinatorics.Line α (Option η) where
  idxFun
    | none => none
    | some e => x e
  proper := ⟨none, rfl⟩

def dhjInsertDistinguished {η α ι : Type*}
    (S : Combinatorics.Subspace η (Option α) ι)
    (hstar : ∃ i, S.idxFun i = Sum.inl none) :
    Combinatorics.Subspace (Option η) α ι where
  idxFun i :=
    match S.idxFun i with
    | Sum.inl none => Sum.inr none
    | Sum.inl (some a) => Sum.inl a
    | Sum.inr e => Sum.inr (some e)
  proper e := by
    cases e with
    | none =>
        obtain ⟨i, hi⟩ := hstar
        exact ⟨i, by simp [hi]⟩
    | some e =>
        obtain ⟨i, hi⟩ := S.proper e
        exact ⟨i, by simp [hi]⟩

def dhjLineTail {α : Type*} {n : ℕ} (l : Combinatorics.Line α (Fin (n + 1)))
    (h : l.idxFun 0 ≠ none) : Combinatorics.Line α (Fin n) where
  idxFun i := l.idxFun i.succ
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    cases i using Fin.cases with
    | zero => exact (h hi).elim
    | succ j => exact ⟨j, hi⟩

def dhjPrependSubspace {n : ℕ} {α ι : Type*}
    (W : Combinatorics.Subspace (Fin n) α ι) :
    Combinatorics.Subspace (Fin (n + 1)) α (Option ι) where
  idxFun
    | none => Sum.inr 0
    | some i => (W.idxFun i).map id Fin.succ
  proper e := by
    cases e using Fin.cases with
    | zero => exact ⟨none, rfl⟩
    | succ e =>
        obtain ⟨i, hi⟩ := W.proper e
        exact ⟨some i, by simp [hi]⟩

def dhjPrependLine {α ι : Type*} (a : α) (l : Combinatorics.Line α ι) :
    Combinatorics.Line α (Option ι) where
  idxFun
    | none => some a
    | some i => l.idxFun i
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨some i, hi⟩

def dhjConsLine {n : ℕ} {α : Type*} (a : α) (l : Combinatorics.Line α (Fin n)) :
    Combinatorics.Line α (Fin (n + 1)) where
  idxFun := Fin.cases (some a) l.idxFun
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i.succ, hi⟩

def dhjPrefixNormal {α κ : Type} :
    (n : ℕ) → (Q : Type) → (Q → Combinatorics.Line α (Fin n) → κ) → Prop
  | 0, _, _ => True
  | n + 1, Q, C =>
      (∀ q l l', l.idxFun 0 = none → l'.idxFun 0 = none → C q l = C q l') ∧
        dhjPrefixNormal n (Q × α) fun qa l => C qa.1 (dhjConsLine qa.2 l)

def dhjSamePrefix {α : Type*} :
    (n : ℕ) → Combinatorics.Line α (Fin n) → Combinatorics.Line α (Fin n) → Prop
  | 0, _, _ => True
  | n + 1, l, l' =>
      (l.idxFun 0 = none ∧ l'.idxFun 0 = none) ∨
        ∃ a t t', l = dhjConsLine a t ∧ l' = dhjConsLine a t' ∧ dhjSamePrefix n t t'

def dhjPrependWord {β : Type*} {s : ℕ} :
    (r : ℕ) → (Fin r → β) → (Fin s → β) → Fin (s + r) → β
  | 0, _, x => x
  | r + 1, p, x => Fin.cases (p 0) (dhjPrependWord r (fun i => p i.succ) x)

def dhjTailIndex (s : ℕ) : (r : ℕ) → Fin s → Fin (s + r)
  | 0 => id
  | r + 1 => fun i => (dhjTailIndex s r i).succ

def dhjPrefixIndex (s : ℕ) : (r : ℕ) → Fin r → Fin (s + r)
  | 0 => Fin.elim0
  | r + 1 => Fin.cases 0 fun i => (dhjPrefixIndex s r i).succ

end MathlibExt.Combinatorics.DensityHalesJewettWanted
