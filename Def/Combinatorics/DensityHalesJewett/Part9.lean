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
import Theorem.Combinatorics.DensityHalesJewett.Part7
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

noncomputable def dhjDensePrefixes {α ι κ : Type*}
    [Fintype α] [Fintype ι] [Fintype κ]
    [Fintype (ι → α)] [Fintype (κ → α)]
    (A : Finset (ι ⊕ κ → α)) (δ : ℝ) : Finset (ι → α) := by
  classical
  exact Finset.univ.filter fun x => δ / 2 ≤ dhjDensity (dhjSection A x)

def dhjExtendSubspace {η α ι κ : Type*}
    (U : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α κ) :
    Combinatorics.Subspace (η ⊕ Unit) α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => (U.idxFun i).map id Sum.inl
    | Sum.inr j => (l.idxFun j).elim (Sum.inr (Sum.inr ())) Sum.inl
  proper
    | Sum.inl e => by
        obtain ⟨i, hi⟩ := U.proper e
        exact ⟨Sum.inl i, by simp [hi]⟩
    | Sum.inr _ => by
        obtain ⟨j, hj⟩ := l.proper
        exact ⟨Sum.inr j, by simp [hj]⟩

def dhjPointSubspace {α ι : Type*} (x : ι → α) :
    Combinatorics.Subspace (Fin 0) α ι where
  idxFun i := Sum.inl (x i)
  proper e := Fin.elim0 e

def dhjMultiAt (k m n : ℕ) (δ : ℝ) : Prop :=
  ∀ A : Finset (Fin n → Fin k), δ ≤ dhjDensity A →
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), dhjSubspaceIn A V

def dhjAppend {X : Type*} {t : ℕ} (p : Fin t → X) (x : X) : Fin (t + 1) → X :=
  Fin.lastCases x p

def dhjBlockAgrees {X : Type*} {L t : ℕ} (p : Fin t → X) (h : t ≤ L)
    (w : Fin L → X) : Prop := ∀ i, w (Fin.castLE h i) = p i

noncomputable def dhjCylinder {X : Type*} {L t : ℕ}
    (A : Finset (Fin L → X)) (p : Fin t → X) (h : t ≤ L) : Finset (Fin L → X) := by
  classical
  exact A.filter (dhjBlockAgrees p h)

noncomputable def dhjCylinderDensity {X : Type*} [Fintype X] {L t : ℕ}
    (A : Finset (Fin L → X)) (p : Fin t → X) (h : t ≤ L) : ℝ :=
  (dhjCylinder A p h).card / (Fintype.card X : ℝ) ^ (L - t)

def dhjFinSplit {L t : ℕ} (h : t ≤ L) : Fin t ⊕ Fin (L - t) ≃ Fin L :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

def dhjBlockJoin {X : Type*} {L t : ℕ} (p : Fin t → X)
    (y : Fin (L - t) → X) (h : t ≤ L) : Fin L → X :=
  dhjConcat p y ∘ (dhjFinSplit h).symm

noncomputable def dhjBlockSection {X : Type*} [Fintype X] {L t : ℕ}
    (A : Finset (Fin L → X)) (p : Fin t → X) (h : t ≤ L) :
    Finset (Fin (L - t) → X) := by
  classical
  exact Finset.univ.filter fun y => dhjBlockJoin p y h ∈ A

def dhjBlockPrefixSubspace {α : Type*} {r t : ℕ}
    (p : Fin t → Fin r → α) :
    Combinatorics.Subspace (Fin r) α (Fin (t + 1) × Fin r) where
  idxFun q := Fin.lastCases (Sum.inr q.2) (fun i => Sum.inl (p i q.2)) q.1
  proper j := ⟨(Fin.last t, j), by simp⟩

noncomputable def dhjColumn {X Ω : Type*} [Fintype X] [Fintype Ω]
    (E : X → Finset Ω) (ω : Ω) : Finset X := by
  classical
  exact Finset.univ.filter fun x => ω ∈ E x

noncomputable def dhjDenseColumns {X Ω : Type*} [Fintype X] [Fintype Ω]
    (E : X → Finset Ω) (α : ℝ) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω => α / 2 ≤ dhjDensity (dhjColumn E ω)

noncomputable def dhjInitialSubspace {α : Type*} [Nonempty α] {d m : ℕ}
    (h : d ≤ m) : Combinatorics.Subspace (Fin d) α (Fin m) where
  idxFun i := if hi : i.val < d then Sum.inr ⟨i.val, hi⟩
    else Sum.inl (Classical.choice ‹Nonempty α›)
  proper j := ⟨Fin.castLE h j, by simp⟩

noncomputable def dhjLineEvent {α ι Ω : Type*}
    [Fintype α] [Fintype Ω] (E : (ι → α) → Finset Ω)
    (l : Combinatorics.Line α ι) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω => ∀ a, ω ∈ E (l a)

def dhjSubspaceMapConstants {η α β ι : Type*} (f : α → β)
    (V : Combinatorics.Subspace η α ι) : Combinatorics.Subspace η β ι where
  idxFun i := (V.idxFun i).map f id
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨i, by simp [hi]⟩

def dhjFixSuffixSubspace {η α ι κ : Type*}
    (V : Combinatorics.Subspace η α ι) (y : κ → α) :
    Combinatorics.Subspace η α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => V.idxFun i
    | Sum.inr j => Sum.inl (y j)
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨Sum.inl i, hi⟩

def dhjBlockSplitEquiv {L t r : ℕ} (h : t ≤ L) :
    (Fin t × Fin r) ⊕ (Fin (L - t) × Fin r) ≃ Fin L × Fin r :=
  (Equiv.sumProdDistrib (Fin t) (Fin (L - t)) (Fin r)).symm.trans
    (Equiv.prodCongr (dhjFinSplit h) (Equiv.refl (Fin r)))

def dhjFlattenBlocks {α : Type*} {L r : ℕ}
    (w : Fin L → Fin r → α) : Fin L × Fin r → α := fun q => w q.1 q.2

def dhjBlockFullSubspace {η α : Type*} {L r t : ℕ}
    (p : Fin t → Fin r → α) (V : Combinatorics.Subspace η α (Fin r))
    (y : Fin (L - (t + 1)) → Fin r → α) (h : t + 1 ≤ L) :
    Combinatorics.Subspace η α (Fin L × Fin r) :=
  (dhjFixSuffixSubspace ((dhjBlockPrefixSubspace p).comp V) (dhjFlattenBlocks y)).reindex
    (Equiv.refl η) (Equiv.refl α) (dhjBlockSplitEquiv h)

noncomputable def dhjSuperlevel {Y : Type*} [Fintype Y]
    (f : Y → ℝ) (c : ℝ) : Finset Y := by
  classical
  exact Finset.univ.filter fun y => c ≤ f y

def dhjDropLast {k : ℕ} {ι : Type*} (i : Fin k)
    (x : ι → Fin (k + 1)) : ι → Fin k := fun q => Fin.lastCases i id (x q)

def dhjReplaceLast {k : ℕ} {ι : Type*} (i : Fin k)
    (x : ι → Fin (k + 1)) : ι → Fin (k + 1) :=
  Fin.castSucc ∘ dhjDropLast i x

def dhjInsensitive {k : ℕ} {ι : Type*} (i : Fin k)
    (D : Finset (ι → Fin (k + 1))) : Prop :=
  ∀ x, x ∈ D ↔ dhjReplaceLast i x ∈ D

noncomputable def dhjInsensitivePreimage {k : ℕ} {ι : Type*}
    [Fintype ι] (B : Finset (ι → Fin (k + 1))) (i : Fin k) :
    Finset (ι → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun x => dhjReplaceLast i x ∈ B

noncomputable def dhjCore {k : ℕ} {ι : Type*} [Fintype ι]
    (B : Finset (ι → Fin (k + 1))) : Finset (ι → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun x => ∀ i : Fin k, dhjReplaceLast i x ∈ B

noncomputable def dhjGoodRestrictedLines {k : ℕ} {ι : Type*}
    [Fintype ι] (B : Finset (ι → Fin (k + 1))) :
    Finset (Combinatorics.Line (Fin k) ι) := by
  classical
  exact Finset.univ.filter fun l => ∀ a : Fin k, Fin.castSucc ∘ l a ∈ B

end MathlibExt.Combinatorics.DensityHalesJewettWanted
