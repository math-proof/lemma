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
import Theorem.Combinatorics.DensityHalesJewett
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

def dhjPointLine {r s : ℕ} {α : Type*} (p : Fin r → α)
    (l : Combinatorics.Line α (Fin s)) : Combinatorics.Line α (Fin (s + r)) where
  idxFun := dhjPrependWord r (some ∘ p) l.idxFun
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨dhjTailIndex s r i, by simpa [dhjPrependWord_tail]⟩

def dhjLinePoint {r s : ℕ} {α : Type*} (l : Combinatorics.Line α (Fin r))
    (x : Fin s → α) : Combinatorics.Line α (Fin (s + r)) where
  idxFun := dhjPrependWord r l.idxFun (some ∘ x)
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨dhjPrefixIndex s r i, by simpa [dhjPrependWord_prefix]⟩

def dhjLineWord {r s : ℕ} {α : Type*} (l : Combinatorics.Line α (Fin r))
    (w : Fin s → Option α) : Combinatorics.Line α (Fin (s + r)) where
  idxFun := dhjPrependWord r l.idxFun w
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨dhjPrefixIndex s r i, by simpa [dhjPrependWord_prefix]⟩

def dhjBlockSubspace {M r s : ℕ} {α : Type*}
    (L : Combinatorics.Line α (Fin r))
    (P : Combinatorics.Subspace (Fin M) α (Fin s)) :
    Combinatorics.Subspace (Fin (M + 1)) α (Fin (s + r)) where
  idxFun := dhjPrependWord r
    (fun i => (L.idxFun i).elim (Sum.inr 0) Sum.inl)
    (fun i => (P.idxFun i).map id Fin.succ)
  proper e := by
    cases e using Fin.cases with
    | zero =>
        obtain ⟨i, hi⟩ := L.proper
        refine ⟨dhjPrefixIndex s r i, ?_⟩
        rw [dhjPrependWord_prefix]
        simp [hi]
    | succ e =>
        obtain ⟨i, hi⟩ := P.proper e
        refine ⟨dhjTailIndex s r i, ?_⟩
        rw [dhjPrependWord_tail]
        simp [hi]

def dhjBlockTailWord {M s : ℕ} {α : Type*}
    (P : Combinatorics.Subspace (Fin M) α (Fin s))
    (u : Combinatorics.Line α (Fin (M + 1))) : Fin s → Option α := fun i =>
  (P.idxFun i).elim some fun e => u.idxFun e.succ

def dhjUsesColors {α κ : Type*} :
    (M : ℕ) → (Combinatorics.Line α (Fin M) → κ) → (Fin M → κ) → Prop
  | 0, _, _ => True
  | M + 1, C, c =>
      (∀ u, u.idxFun 0 = none → C u = c 0) ∧
        ∀ a, dhjUsesColors M (fun u => C (dhjConsLine a u)) (fun i => c i.succ)

noncomputable def dhjCoordinateSubspace {α : Type*} [Nonempty α] {M m : ℕ}
    (t : Finset (Fin M)) (ht : t.card = m) :
    Combinatorics.Subspace (Fin m) α (Fin M) := by
  let e : t ≃ Fin m := Fintype.equivFinOfCardEq ((Fintype.card_coe t).trans ht)
  exact
    { idxFun := fun i =>
        if h : i ∈ t then Sum.inr (e ⟨i, h⟩)
        else Sum.inl (Classical.choice ‹Nonempty α›)
      proper := by
        intro j
        refine ⟨(e.symm j).1, ?_⟩
        simp [e] }

def dhjTailWord {n : ℕ} {α ι : Type*}
    (W : Combinatorics.Subspace (Fin n) α ι)
    (l : Combinatorics.Line α (Fin (n + 1))) : ι → Option α := fun i =>
  (W.idxFun i).elim some fun e => l.idxFun e.succ

noncomputable def dhjDensity {X : Type*} [Fintype X] (A : Finset X) : ℝ :=
  A.card / Fintype.card X

def dhjConcat {α ι κ : Type*} (x : ι → α) (y : κ → α) : ι ⊕ κ → α :=
  Sum.elim x y

noncomputable def dhjSection {α ι κ : Type*}
    [Fintype α] [Fintype ι] [Fintype κ]
    (A : Finset (ι ⊕ κ → α)) (x : ι → α) : Finset (κ → α) := by
  classical
  exact Finset.univ.filter fun y => dhjConcat x y ∈ A

def dhjPrefixLine {α ι κ : Type*} (x : ι → α)
    (l : Combinatorics.Line α κ) : Combinatorics.Line α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => some (x i)
    | Sum.inr j => l.idxFun j
  proper := by
    obtain ⟨j, hj⟩ := l.proper
    exact ⟨Sum.inr j, hj⟩

def dhjLineIn {α ι : Type*} (A : Finset (ι → α))
    (l : Combinatorics.Line α ι) : Prop := ∀ a, l a ∈ A

end MathlibExt.Combinatorics.DensityHalesJewettWanted
