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

private def dhjDistinguishedLine {η α : Type*} (x : η → Option α) :
    Combinatorics.Line α (Option η) where
  idxFun
    | none => none
    | some e => x e
  proper := ⟨none, rfl⟩

private def dhjInsertDistinguished {η α ι : Type*}
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

private def dhjLineTail {α : Type*} {n : ℕ} (l : Combinatorics.Line α (Fin (n + 1)))
    (h : l.idxFun 0 ≠ none) : Combinatorics.Line α (Fin n) where
  idxFun i := l.idxFun i.succ
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    cases i using Fin.cases with
    | zero => exact (h hi).elim
    | succ j => exact ⟨j, hi⟩

private def dhjPrependSubspace {n : ℕ} {α ι : Type*}
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

private def dhjPrependLine {α ι : Type*} (a : α) (l : Combinatorics.Line α ι) :
    Combinatorics.Line α (Option ι) where
  idxFun
    | none => some a
    | some i => l.idxFun i
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨some i, hi⟩

private def dhjConsLine {n : ℕ} {α : Type*} (a : α) (l : Combinatorics.Line α (Fin n)) :
    Combinatorics.Line α (Fin (n + 1)) where
  idxFun := Fin.cases (some a) l.idxFun
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i.succ, hi⟩

private def dhjPrefixNormal {α κ : Type} :
    (n : ℕ) → (Q : Type) → (Q → Combinatorics.Line α (Fin n) → κ) → Prop
  | 0, _, _ => True
  | n + 1, Q, C =>
      (∀ q l l', l.idxFun 0 = none → l'.idxFun 0 = none → C q l = C q l') ∧
        dhjPrefixNormal n (Q × α) fun qa l => C qa.1 (dhjConsLine qa.2 l)

private def dhjSamePrefix {α : Type*} :
    (n : ℕ) → Combinatorics.Line α (Fin n) → Combinatorics.Line α (Fin n) → Prop
  | 0, _, _ => True
  | n + 1, l, l' =>
      (l.idxFun 0 = none ∧ l'.idxFun 0 = none) ∨
        ∃ a t t', l = dhjConsLine a t ∧ l' = dhjConsLine a t' ∧ dhjSamePrefix n t t'

private def dhjPrependWord {β : Type*} {s : ℕ} :
    (r : ℕ) → (Fin r → β) → (Fin s → β) → Fin (s + r) → β
  | 0, _, x => x
  | r + 1, p, x => Fin.cases (p 0) (dhjPrependWord r (fun i => p i.succ) x)

private def dhjTailIndex (s : ℕ) : (r : ℕ) → Fin s → Fin (s + r)
  | 0 => id
  | r + 1 => fun i => (dhjTailIndex s r i).succ

private def dhjPrefixIndex (s : ℕ) : (r : ℕ) → Fin r → Fin (s + r)
  | 0 => Fin.elim0
  | r + 1 => Fin.cases 0 fun i => (dhjPrefixIndex s r i).succ

private theorem dhjPrependWord_tail {β : Type*} {r s : ℕ}
    (p : Fin r → β) (x : Fin s → β) (i : Fin s) :
    dhjPrependWord r p x (dhjTailIndex s r i) = x i := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih (fun j => p j.succ)

private theorem dhjPrependWord_prefix {β : Type*} {r s : ℕ}
    (p : Fin r → β) (x : Fin s → β) (i : Fin r) :
    dhjPrependWord r p x (dhjPrefixIndex s r i) = p i := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact ih (fun j => p j.succ) i

private def dhjPointLine {r s : ℕ} {α : Type*} (p : Fin r → α)
    (l : Combinatorics.Line α (Fin s)) : Combinatorics.Line α (Fin (s + r)) where
  idxFun := dhjPrependWord r (some ∘ p) l.idxFun
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨dhjTailIndex s r i, by simpa [dhjPrependWord_tail]⟩

private def dhjLinePoint {r s : ℕ} {α : Type*} (l : Combinatorics.Line α (Fin r))
    (x : Fin s → α) : Combinatorics.Line α (Fin (s + r)) where
  idxFun := dhjPrependWord r l.idxFun (some ∘ x)
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨dhjPrefixIndex s r i, by simpa [dhjPrependWord_prefix]⟩

private def dhjLineWord {r s : ℕ} {α : Type*} (l : Combinatorics.Line α (Fin r))
    (w : Fin s → Option α) : Combinatorics.Line α (Fin (s + r)) where
  idxFun := dhjPrependWord r l.idxFun w
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨dhjPrefixIndex s r i, by simpa [dhjPrependWord_prefix]⟩

private def dhjBlockSubspace {M r s : ℕ} {α : Type*}
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

private def dhjBlockTailWord {M s : ℕ} {α : Type*}
    (P : Combinatorics.Subspace (Fin M) α (Fin s))
    (u : Combinatorics.Line α (Fin (M + 1))) : Fin s → Option α := fun i =>
  (P.idxFun i).elim some fun e => u.idxFun e.succ

private def dhjUsesColors {α κ : Type*} :
    (M : ℕ) → (Combinatorics.Line α (Fin M) → κ) → (Fin M → κ) → Prop
  | 0, _, _ => True
  | M + 1, C, c =>
      (∀ u, u.idxFun 0 = none → C u = c 0) ∧
        ∀ a, dhjUsesColors M (fun u => C (dhjConsLine a u)) (fun i => c i.succ)

private noncomputable def dhjCoordinateSubspace {α : Type*} [Nonempty α] {M m : ℕ}
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

private def dhjTailWord {n : ℕ} {α ι : Type*}
    (W : Combinatorics.Subspace (Fin n) α ι)
    (l : Combinatorics.Line α (Fin (n + 1))) : ι → Option α := fun i =>
  (W.idxFun i).elim some fun e => l.idxFun e.succ

private noncomputable def dhjDensity {X : Type*} [Fintype X] (A : Finset X) : ℝ :=
  A.card / Fintype.card X

private def dhjConcat {α ι κ : Type*} (x : ι → α) (y : κ → α) : ι ⊕ κ → α :=
  Sum.elim x y

private noncomputable def dhjSection {α ι κ : Type*}
    [Fintype α] [Fintype ι] [Fintype κ]
    (A : Finset (ι ⊕ κ → α)) (x : ι → α) : Finset (κ → α) := by
  classical
  exact Finset.univ.filter fun y => dhjConcat x y ∈ A

private def dhjPrefixLine {α ι κ : Type*} (x : ι → α)
    (l : Combinatorics.Line α κ) : Combinatorics.Line α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => some (x i)
    | Sum.inr j => l.idxFun j
  proper := by
    obtain ⟨j, hj⟩ := l.proper
    exact ⟨Sum.inr j, hj⟩

private def dhjLineIn {α ι : Type*} (A : Finset (ι → α))
    (l : Combinatorics.Line α ι) : Prop := ∀ a, l a ∈ A

private noncomputable instance dhjFiniteLine {α ι : Type*} [Finite α] [Finite ι] :
    Finite (Combinatorics.Line α ι) :=
  Finite.of_injective Combinatorics.Line.idxFun fun _ _ h => Combinatorics.Line.ext h

private noncomputable instance dhjFintypeLine {α ι : Type*} [Fintype α] [Fintype ι] :
    Fintype (Combinatorics.Line α ι) := Fintype.ofFinite _

private noncomputable instance dhjFiniteSubspace {η α ι : Type*}
    [Finite η] [Finite α] [Finite ι] :
    Finite (Combinatorics.Subspace η α ι) :=
  Finite.of_injective Combinatorics.Subspace.idxFun fun _ _ h =>
    Combinatorics.Subspace.ext h

private noncomputable instance dhjFintypeSubspace {η α ι : Type*}
    [Fintype η] [Fintype α] [Fintype ι] :
    Fintype (Combinatorics.Subspace η α ι) := Fintype.ofFinite _

private theorem dhjSubspace_apply_injective {η α ι : Type*}
    (V : Combinatorics.Subspace η α ι) : Function.Injective V := by
  intro x y hxy
  funext e
  obtain ⟨i, hi⟩ := V.proper e
  have hi' := congrFun hxy i
  simpa [Combinatorics.Subspace.coe_apply, hi] using hi'

private noncomputable def dhjSubspacePoints {η α ι : Type*}
    [Fintype η] [Fintype α] (V : Combinatorics.Subspace η α ι) :
    Finset (ι → α) := by
  classical
  exact Finset.univ.map ⟨V, dhjSubspace_apply_injective V⟩

private inductive dhjTiled (d k : ℕ) {ι : Type*}
    [DecidableEq (ι → Fin (k + 1))] :
    Finset (ι → Fin (k + 1)) → Prop
  | empty : dhjTiled d k ∅
  | add (C : Finset (ι → Fin (k + 1)))
      (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) ι) :
      dhjTiled d k C → Disjoint C (dhjSubspacePoints V) →
        dhjTiled d k (C ∪ dhjSubspacePoints V)

private noncomputable def dhjLineCount (k n : ℕ) : ℕ :=
  Nat.card (Combinatorics.Line (Fin k) (Fin n))

private def dhjLiftLine {k : ℕ} {ι : Type*} (l : Combinatorics.Line (Fin k) ι) :
    Combinatorics.Line (Fin (k + 1)) ι where
  idxFun i := (l.idxFun i).map Fin.castSucc
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i, by simp [hi]⟩

private def dhjLineTop {k : ℕ} {ι : Type*}
    (l : Combinatorics.Line (Fin k) ι) : ι → Fin (k + 1) :=
  dhjLiftLine l (Fin.last k)

private def dhjHasLast {k : ℕ} {ι : Type*} (x : ι → Fin (k + 1)) : Prop :=
  ¬∀ i, x i ≠ Fin.last k

private theorem dhjLineTop_hasLast {k : ℕ} {ι : Type*}
    (l : Combinatorics.Line (Fin k) ι) : dhjHasLast (dhjLineTop l) := by
  obtain ⟨i, hi⟩ := l.proper
  intro h
  exact h i (by simp [dhjLineTop, dhjLiftLine, Combinatorics.Line.coe_apply, hi])

private def dhjLineOfTop {k : ℕ} {ι : Type*} (x : ι → Fin (k + 1))
    (hx : dhjHasLast x) : Combinatorics.Line (Fin k) ι where
  idxFun i := Fin.lastCases none some (x i)
  proper := by
    rw [dhjHasLast] at hx
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by simp [hi]⟩

@[simp]
private theorem dhjLineTop_lineOfTop {k : ℕ} {ι : Type*} (x : ι → Fin (k + 1))
    (hx : dhjHasLast x) : dhjLineTop (dhjLineOfTop x hx) = x := by
  funext i
  generalize hxi : x i = a
  cases a using Fin.lastCases <;>
    simp [dhjLineTop, dhjLiftLine, dhjLineOfTop, Combinatorics.Line.coe_apply, hxi]

@[simp]
private theorem dhjLineOfTop_lineTop {k : ℕ} {ι : Type*}
    (l : Combinatorics.Line (Fin k) ι) :
    dhjLineOfTop (dhjLineTop l) (dhjLineTop_hasLast l) = l := by
  apply Combinatorics.Line.ext
  funext i
  cases hi : l.idxFun i <;>
    simp [dhjLineOfTop, dhjLineTop, dhjLiftLine, Combinatorics.Line.coe_apply, hi]

private def dhjLineTopEquiv {k : ℕ} {ι : Type*} :
    Combinatorics.Line (Fin k) ι ≃ {x : ι → Fin (k + 1) // dhjHasLast x} where
  toFun l := ⟨dhjLineTop l, dhjLineTop_hasLast l⟩
  invFun x := dhjLineOfTop x x.2
  left_inv := dhjLineOfTop_lineTop
  right_inv x := by
    apply Subtype.ext
    exact dhjLineTop_lineOfTop x.1 x.2

private def dhjNoLastEquiv {k : ℕ} {ι : Type*} :
    {x : ι → Fin (k + 1) // ∀ i, x i ≠ Fin.last k} ≃ (ι → Fin k) where
  toFun x i := (x.1 i).castPred (x.2 i)
  invFun x := ⟨Fin.castSucc ∘ x, fun i => Fin.castSucc_ne_last _⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact Fin.castSucc_castPred _ _
  right_inv x := by
    funext i
    exact Fin.castPred_castSucc _

private def dhjAt (k n : ℕ) (δ : ℝ) : Prop :=
  ∀ A : Finset (Fin n → Fin k), δ ≤ dhjDensity A →
    ∃ l : Combinatorics.Line (Fin k) (Fin n), dhjLineIn A l

private def dhjThreshold (k : ℕ) (δ : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, dhjAt k n δ

private noncomputable def dhjPullback {η α ι : Type*}
    [Fintype η] [Fintype α] [Fintype (η → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : Finset (η → α) := by
  classical
  exact Finset.univ.filter fun x => V x ∈ A

private noncomputable def dhjDensityOn {η α ι : Type*}
    [Fintype η] [Fintype α] [Fintype (η → α)]
    (A : Finset (ι → α)) (V : Combinatorics.Subspace η α ι) : ℝ :=
  dhjDensity (dhjPullback V A)

private def dhjSubspaceIn {η α ι : Type*} (A : Finset (ι → α))
    (V : Combinatorics.Subspace η α ι) : Prop := ∀ x, V x ∈ A

private def dhjSupport {ι : Type*} [Fintype ι] (x : ι → Fin 2) : Finset ι :=
  Finset.univ.filter fun i => x i = 1

@[simp]
private theorem dhj_mem_support {ι : Type*} [Fintype ι] (x : ι → Fin 2) (i : ι) :
    i ∈ dhjSupport x ↔ x i = 1 := by
  simp [dhjSupport]

private theorem dhjSupport_injective {ι : Type*} [Fintype ι] :
    Function.Injective (dhjSupport : (ι → Fin 2) → Finset ι) := by
  intro x y hxy
  funext i
  have hi : x i = 1 ↔ y i = 1 := by
    simpa only [dhj_mem_support] using Finset.ext_iff.mp hxy i
  apply Fin.ext
  omega

private def dhjLineOfSupport {ι : Type*} [Fintype ι] (x y : ι → Fin 2)
    (hxy : dhjSupport x ⊂ dhjSupport y) : Combinatorics.Line (Fin 2) ι where
  idxFun i := if x i = y i then some (x i) else none
  proper := by
    obtain ⟨i, hiy, hix⟩ := Finset.exists_of_ssubset hxy
    have hne : x i ≠ y i := by
      intro hi
      have hy : y i = 1 := dhj_mem_support y i |>.mp hiy
      exact hix (dhj_mem_support x i |>.mpr (hi.trans hy))
    exact ⟨i, by simp [hne]⟩

@[simp]
private theorem dhjLineOfSupport_zero {ι : Type*} [Fintype ι] (x y : ι → Fin 2)
    (hxy : dhjSupport x ⊂ dhjSupport y) : dhjLineOfSupport x y hxy 0 = x := by
  funext i
  by_cases hi : x i = y i
  · simp [dhjLineOfSupport, Combinatorics.Line.coe_apply, hi]
  · have hsub := hxy.1
    have hx : x i ≠ 1 := by
      intro hx
      have hy := hsub (dhj_mem_support x i |>.mpr hx)
      exact hi (hx.trans (dhj_mem_support y i |>.mp hy).symm)
    have hx0 : x i = 0 := by
      apply Fin.ext
      omega
    have hne : (0 : Fin 2) ≠ y i := by
      intro h
      exact hi (hx0.trans h)
    simp [dhjLineOfSupport, Combinatorics.Line.coe_apply, hx0, hne]

@[simp]
private theorem dhjLineOfSupport_one {ι : Type*} [Fintype ι] (x y : ι → Fin 2)
    (hxy : dhjSupport x ⊂ dhjSupport y) : dhjLineOfSupport x y hxy 1 = y := by
  funext i
  by_cases hi : x i = y i
  · simp [dhjLineOfSupport, Combinatorics.Line.coe_apply, hi]
  · have hsub := hxy.1
    have himp : x i = 1 → y i = 1 := by
      intro hx
      exact dhj_mem_support y i |>.mp (hsub (dhj_mem_support x i |>.mpr hx))
    have hy : y i = 1 := by
      apply Fin.ext
      omega
    have hx : x i ≠ 1 := by
      intro hx
      exact hi (hx.trans hy.symm)
    simp [dhjLineOfSupport, Combinatorics.Line.coe_apply, hy, hx]

private def dhjLineFree {α ι : Type*} (A : Finset (ι → α)) : Prop :=
  ∀ l : Combinatorics.Line α ι, ¬dhjLineIn A l

private theorem dhj_lineFree_card_le_middle {n : ℕ} (A : Finset (Fin n → Fin 2))
    (hA : dhjLineFree A) : A.card ≤ n.choose (n / 2) := by
  classical
  have hsperner := (dhj_supports_antichain A hA).sperner
  rw [Finset.card_image_of_injective A dhjSupport_injective] at hsperner
  simpa using hsperner

private theorem dhj_lineFree_density_le_central (r : ℕ)
    (A : Finset (Fin (2 * r) → Fin 2)) (hA : dhjLineFree A) :
    dhjDensity A ≤ (Nat.centralBinom r : ℝ) / 4 ^ r := by
  have hcard : A.card ≤ Nat.centralBinom r := by
    simpa [Nat.centralBinom, Nat.mul_div_cancel_left] using dhj_lineFree_card_le_middle A hA
  have hcube : Fintype.card (Fin (2 * r) → Fin 2) = 4 ^ r := by
    simp [pow_mul]
  rw [dhjDensity, hcube]
  rw [Nat.cast_pow]
  norm_num only [Nat.cast_ofNat]
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast hcard

private theorem dhjThreshold_two {δ : ℝ} (hδ : 0 < δ) : dhjThreshold 2 δ := by
  obtain ⟨r, hr⟩ := dhj_exists_centralBinom_ratio_lt hδ
  apply dhjThreshold_of_at (k := 2) (N := 2 * r) (by omega)
  intro A hden
  by_contra hline
  have hfree : dhjLineFree A := by
    intro l hl
    exact hline ⟨l, hl⟩
  have hupper := dhj_lineFree_density_le_central r A hfree
  linarith

private noncomputable def dhjDensePrefixes {α ι κ : Type*}
    [Fintype α] [Fintype ι] [Fintype κ]
    [Fintype (ι → α)] [Fintype (κ → α)]
    (A : Finset (ι ⊕ κ → α)) (δ : ℝ) : Finset (ι → α) := by
  classical
  exact Finset.univ.filter fun x => δ / 2 ≤ dhjDensity (dhjSection A x)

private def dhjExtendSubspace {η α ι κ : Type*}
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

private def dhjPointSubspace {α ι : Type*} (x : ι → α) :
    Combinatorics.Subspace (Fin 0) α ι where
  idxFun i := Sum.inl (x i)
  proper e := Fin.elim0 e

private def dhjMultiAt (k m n : ℕ) (δ : ℝ) : Prop :=
  ∀ A : Finset (Fin n → Fin k), δ ≤ dhjDensity A →
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), dhjSubspaceIn A V

private def dhjAppend {X : Type*} {t : ℕ} (p : Fin t → X) (x : X) : Fin (t + 1) → X :=
  Fin.lastCases x p

private def dhjBlockAgrees {X : Type*} {L t : ℕ} (p : Fin t → X) (h : t ≤ L)
    (w : Fin L → X) : Prop := ∀ i, w (Fin.castLE h i) = p i

private noncomputable def dhjCylinder {X : Type*} {L t : ℕ}
    (A : Finset (Fin L → X)) (p : Fin t → X) (h : t ≤ L) : Finset (Fin L → X) := by
  classical
  exact A.filter (dhjBlockAgrees p h)

private noncomputable def dhjCylinderDensity {X : Type*} [Fintype X] {L t : ℕ}
    (A : Finset (Fin L → X)) (p : Fin t → X) (h : t ≤ L) : ℝ :=
  (dhjCylinder A p h).card / (Fintype.card X : ℝ) ^ (L - t)

private def dhjFinSplit {L t : ℕ} (h : t ≤ L) : Fin t ⊕ Fin (L - t) ≃ Fin L :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

private def dhjBlockJoin {X : Type*} {L t : ℕ} (p : Fin t → X)
    (y : Fin (L - t) → X) (h : t ≤ L) : Fin L → X :=
  dhjConcat p y ∘ (dhjFinSplit h).symm

private noncomputable def dhjBlockSection {X : Type*} [Fintype X] {L t : ℕ}
    (A : Finset (Fin L → X)) (p : Fin t → X) (h : t ≤ L) :
    Finset (Fin (L - t) → X) := by
  classical
  exact Finset.univ.filter fun y => dhjBlockJoin p y h ∈ A

private def dhjBlockPrefixSubspace {α : Type*} {r t : ℕ}
    (p : Fin t → Fin r → α) :
    Combinatorics.Subspace (Fin r) α (Fin (t + 1) × Fin r) where
  idxFun q := Fin.lastCases (Sum.inr q.2) (fun i => Sum.inl (p i q.2)) q.1
  proper j := ⟨(Fin.last t, j), by simp⟩

private noncomputable def dhjColumn {X Ω : Type*} [Fintype X] [Fintype Ω]
    (E : X → Finset Ω) (ω : Ω) : Finset X := by
  classical
  exact Finset.univ.filter fun x => ω ∈ E x

private noncomputable def dhjDenseColumns {X Ω : Type*} [Fintype X] [Fintype Ω]
    (E : X → Finset Ω) (α : ℝ) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω => α / 2 ≤ dhjDensity (dhjColumn E ω)

private noncomputable def dhjInitialSubspace {α : Type*} [Nonempty α] {d m : ℕ}
    (h : d ≤ m) : Combinatorics.Subspace (Fin d) α (Fin m) where
  idxFun i := if hi : i.val < d then Sum.inr ⟨i.val, hi⟩
    else Sum.inl (Classical.choice ‹Nonempty α›)
  proper j := ⟨Fin.castLE h j, by simp⟩

private noncomputable def dhjLineEvent {α ι Ω : Type*}
    [Fintype α] [Fintype Ω] (E : (ι → α) → Finset Ω)
    (l : Combinatorics.Line α ι) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω => ∀ a, ω ∈ E (l a)

private def dhjSubspaceMapConstants {η α β ι : Type*} (f : α → β)
    (V : Combinatorics.Subspace η α ι) : Combinatorics.Subspace η β ι where
  idxFun i := (V.idxFun i).map f id
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨i, by simp [hi]⟩

private def dhjFixSuffixSubspace {η α ι κ : Type*}
    (V : Combinatorics.Subspace η α ι) (y : κ → α) :
    Combinatorics.Subspace η α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => V.idxFun i
    | Sum.inr j => Sum.inl (y j)
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨Sum.inl i, hi⟩

private def dhjBlockSplitEquiv {L t r : ℕ} (h : t ≤ L) :
    (Fin t × Fin r) ⊕ (Fin (L - t) × Fin r) ≃ Fin L × Fin r :=
  (Equiv.sumProdDistrib (Fin t) (Fin (L - t)) (Fin r)).symm.trans
    (Equiv.prodCongr (dhjFinSplit h) (Equiv.refl (Fin r)))

private def dhjFlattenBlocks {α : Type*} {L r : ℕ}
    (w : Fin L → Fin r → α) : Fin L × Fin r → α := fun q => w q.1 q.2

private def dhjBlockFullSubspace {η α : Type*} {L r t : ℕ}
    (p : Fin t → Fin r → α) (V : Combinatorics.Subspace η α (Fin r))
    (y : Fin (L - (t + 1)) → Fin r → α) (h : t + 1 ≤ L) :
    Combinatorics.Subspace η α (Fin L × Fin r) :=
  (dhjFixSuffixSubspace ((dhjBlockPrefixSubspace p).comp V) (dhjFlattenBlocks y)).reindex
    (Equiv.refl η) (Equiv.refl α) (dhjBlockSplitEquiv h)

private noncomputable def dhjSuperlevel {Y : Type*} [Fintype Y]
    (f : Y → ℝ) (c : ℝ) : Finset Y := by
  classical
  exact Finset.univ.filter fun y => c ≤ f y

private def dhjDropLast {k : ℕ} {ι : Type*} (i : Fin k)
    (x : ι → Fin (k + 1)) : ι → Fin k := fun q => Fin.lastCases i id (x q)

private def dhjReplaceLast {k : ℕ} {ι : Type*} (i : Fin k)
    (x : ι → Fin (k + 1)) : ι → Fin (k + 1) :=
  Fin.castSucc ∘ dhjDropLast i x

private def dhjInsensitive {k : ℕ} {ι : Type*} (i : Fin k)
    (D : Finset (ι → Fin (k + 1))) : Prop :=
  ∀ x, x ∈ D ↔ dhjReplaceLast i x ∈ D

private noncomputable def dhjInsensitivePreimage {k : ℕ} {ι : Type*}
    [Fintype ι] (B : Finset (ι → Fin (k + 1))) (i : Fin k) :
    Finset (ι → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun x => dhjReplaceLast i x ∈ B

private noncomputable def dhjCore {k : ℕ} {ι : Type*} [Fintype ι]
    (B : Finset (ι → Fin (k + 1))) : Finset (ι → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun x => ∀ i : Fin k, dhjReplaceLast i x ∈ B

private noncomputable def dhjGoodRestrictedLines {k : ℕ} {ι : Type*}
    [Fintype ι] (B : Finset (ι → Fin (k + 1))) :
    Finset (Combinatorics.Line (Fin k) ι) := by
  classical
  exact Finset.univ.filter fun l => ∀ a : Fin k, Fin.castSucc ∘ l a ∈ B

private theorem dhjLineTop_injective {k : ℕ} {ι : Type*} :
    Function.Injective (dhjLineTop : Combinatorics.Line (Fin k) ι → ι → Fin (k + 1)) := by
  intro l l' h
  rw [← dhjLineOfTop_lineTop l, ← dhjLineOfTop_lineTop l']
  congr

private theorem dhj_lineFree_inter_core_noLast {k m : ℕ}
    (B : Finset (Fin m → Fin (k + 1))) (hB : dhjLineFree B) :
    ∀ x ∈ B ∩ dhjCore B, ∀ q, x q ≠ Fin.last k := by
  classical
  intro x hx q hxq
  have hxB : x ∈ B := (Finset.mem_inter.mp hx).1
  have hxC : x ∈ dhjCore B := (Finset.mem_inter.mp hx).2
  have hxlast : dhjHasLast x := by
    rw [dhjHasLast]
    intro h
    exact h q hxq
  let l := dhjLineOfTop x hxlast
  apply hB (dhjLiftLine l)
  intro a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have htop : dhjLineTop l = x := dhjLineTop_lineOfTop x hxlast
    change dhjLineTop l ∈ B
    rw [htop]
    exact hxB
  · rw [dhjLiftLine_apply]
    have hreplace : dhjReplaceLast i x = Fin.castSucc ∘ l i := by
      rw [← dhjLineTop_lineOfTop x hxlast]
      exact dhjReplaceLast_lineTop i l
    rw [← hreplace]
    exact (dhj_mem_core B x).mp hxC i

private theorem dhj_inter_core_density_le_ratio {k m : ℕ}
    (B : Finset (Fin m → Fin (k + 1))) (hB : dhjLineFree B) :
    dhjDensity (B ∩ dhjCore B) ≤ ((k : ℝ) / (k + 1)) ^ m := by
  classical
  let S : Finset (Fin m → Fin (k + 1)) :=
    Finset.univ.filter fun x => ∀ q, x q ≠ Fin.last k
  have hsub : B ∩ dhjCore B ⊆ S := by
    intro x hx
    simpa [S] using dhj_lineFree_inter_core_noLast B hB x hx
  apply (dhjDensity_mono hsub).trans_eq
  rw [dhjDensity]
  have hcardS : S.card = k ^ m := by
    rw [show S.card = Fintype.card {x : Fin m → Fin (k + 1) //
        ∀ q, x q ≠ Fin.last k} by
      rw [Fintype.card_subtype]]
    rw [Fintype.card_congr (dhjNoLastEquiv (k := k) (ι := Fin m))]
    simp
  rw [hcardS]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [div_pow]
  norm_num

private theorem dhj_lemma10_cube {k m : ℕ} {δ η θ : ℝ}
    (hk : 0 < k) (hm : k ≤ m) (hδ : 0 < δ) (hθ : 0 ≤ θ)
    (hη : η = δ * θ / 48)
    (hratio : ((k : ℝ) / (k + 1)) ^ m ≤ η)
    (B : Finset (Fin m → Fin (k + 1))) (hB : dhjLineFree B)
    (hden : δ - 2 * η ≤ dhjDensity B)
    (hgood : θ / 2 ≤ dhjDensity (dhjGoodRestrictedLines B)) :
    let C := dhjCore B
    θ / 4 ≤ dhjDensity C ∧
      (∀ i : Fin k, dhjInsensitive i (dhjInsensitivePreimage B i)) ∧
      (∀ x, x ∈ C ↔ ∀ i : Fin k, x ∈ dhjInsensitivePreimage B i) ∧
      δ - 3 * η ≤ dhjDensity (B \ C) ∧
      (δ + 6 * η) * dhjDensity (Finset.univ \ C) ≤ dhjDensity (B \ C) := by
  classical
  dsimp only
  have hC : θ / 4 ≤ dhjDensity (dhjCore B) :=
    dhj_core_density_lower hk hm hθ B hgood
  have hBC : dhjDensity (B ∩ dhjCore B) ≤ η :=
    (dhj_inter_core_density_le_ratio B hB).trans hratio
  have hpartition := dhj_density_inter_add_sdiff B (dhjCore B)
  have hdiff : δ - 3 * η ≤ dhjDensity (B \ dhjCore B) := by
    linarith
  have hcomp : dhjDensity (Finset.univ \ dhjCore B) =
      1 - dhjDensity (dhjCore B) := dhj_density_compl (dhjCore B)
  have hcompUpper : dhjDensity (Finset.univ \ dhjCore B) ≤ 1 - θ / 4 := by
    rw [hcomp]
    linarith
  have hηnonneg : 0 ≤ η := by rw [hη]; positivity
  have hcoef : 0 ≤ δ + 6 * η := by positivity
  have hnumeric : (δ + 6 * η) * (1 - θ / 4) ≤ δ - 3 * η := by
    rw [hη]
    nlinarith [mul_nonneg hδ.le (sq_nonneg θ)]
  refine ⟨hC, fun i => dhjInsensitive_preimage B i,
    fun x => dhj_mem_core_iff_preimages B x, hdiff, ?_⟩
  calc
    (δ + 6 * η) * dhjDensity (Finset.univ \ dhjCore B) ≤
        (δ + 6 * η) * (1 - θ / 4) := mul_le_mul_of_nonneg_left hcompUpper hcoef
    _ ≤ δ - 3 * η := hnumeric
    _ ≤ dhjDensity (B \ dhjCore B) := hdiff

private noncomputable def dhjFiber {X I : Type*} [Fintype X]
    (Q : Finset X) (f : X → I) (i : I) : Finset X := by
  classical
  exact Q.filter fun x => f x = i

private noncomputable def dhjBadIndices {k : ℕ} {ι : Type*} [Fintype ι]
    (B : Finset (ι → Fin (k + 1))) (x : ι → Fin (k + 1)) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun i => x ∉ dhjInsensitivePreimage B i

private noncomputable def dhjFirstBad {k : ℕ} {ι : Type*} [Fintype ι]
    (i₀ : Fin k) (B : Finset (ι → Fin (k + 1))) (x : ι → Fin (k + 1)) : Fin k :=
  if h : (dhjBadIndices B x).Nonempty then (dhjBadIndices B x).min' h else i₀

private noncomputable def dhjCell {k : ℕ} {ι : Type*} [Fintype ι]
    (B : Finset (ι → Fin (k + 1))) (i : Fin k) : Finset (ι → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun x =>
    x ∉ dhjInsensitivePreimage B i ∧
      ∀ j : Fin k, j < i → x ∈ dhjInsensitivePreimage B j

private noncomputable def dhjCellFactor {k : ℕ} {ι : Type*} [Fintype ι]
    [Fintype (ι → Fin (k + 1))] (B : Finset (ι → Fin (k + 1)))
    (i j : Fin k) : Finset (ι → Fin (k + 1)) :=
  if j < i then dhjInsensitivePreimage B j
  else if j = i then Finset.univ \ dhjInsensitivePreimage B j
  else Finset.univ

private noncomputable def dhjFamilyMeet {k : ℕ} {ι : Type*} [Fintype ι]
    (D : Fin k → Finset (ι → Fin (k + 1))) : Finset (ι → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun x => ∀ i, x ∈ D i

private theorem dhj_corollary11_cube {k m : ℕ} {δ η θ γ : ℝ}
    (hk : 0 < k) (hm : k ≤ m) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hθ : 0 < θ) (hθle : θ ≤ 1) (hη : η = δ * θ / 48)
    (hγ : γ = δ * η ^ 2 / k)
    (hratio : ((k : ℝ) / (k + 1)) ^ m ≤ η)
    (B : Finset (Fin m → Fin (k + 1))) (hB : dhjLineFree B)
    (hden : δ - 2 * η ≤ dhjDensity B)
    (hgood : θ / 2 ≤ dhjDensity (dhjGoodRestrictedLines B)) :
    ∃ D : Fin k → Finset (Fin m → Fin (k + 1)),
      (∀ i, dhjInsensitive i (D i)) ∧
        γ ≤ dhjDensity (dhjFamilyMeet D) ∧
        (δ + γ) * dhjDensity (dhjFamilyMeet D) ≤
          dhjDensity (B ∩ dhjFamilyMeet D) := by
  classical
  obtain ⟨hC, hCi, hCeq, hdiff, hcorr⟩ :=
    dhj_lemma10_cube hk hm hδ hθ.le hη hratio B hB hden hgood
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηle : η ≤ δ / 48 := by
    rw [hη]
    gcongr
    exact mul_le_of_le_one_right hδ.le hθle
  have hδ3η : 0 < δ - 3 * η := by
    nlinarith
  let Q : Finset (Fin m → Fin (k + 1)) := Finset.univ \ dhjCore B
  have hBQ : B ∩ Q = B \ dhjCore B := by
    ext x
    simp [Q]
  have hBQsub : B \ dhjCore B ⊆ Q := by
    intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
  have hQlower : δ - 3 * η ≤ dhjDensity Q :=
    hdiff.trans (dhjDensity_mono hBQsub)
  have hQpos : 0 < dhjDensity Q := hδ3η.trans_le hQlower
  let i₀ : Fin k := ⟨0, hk⟩
  obtain ⟨i, hiMass, hiCorr⟩ := dhj_exists_large_correlated_fiber hk B Q
    (dhjFirstBad i₀ B) hδ hηpos hQpos (by simpa [hBQ] using hcorr)
  have hfiber : dhjFiber Q (dhjFirstBad i₀ B) i = dhjCell B i := by
    exact dhj_fiber_firstBad_eq_cell i₀ B i
  rw [hfiber] at hiMass hiCorr
  let D := dhjCellFactor B i
  have hmeet : dhjFamilyMeet D = dhjCell B i := dhj_familyMeet_cellFactor B i
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hηone : η ≤ 1 := hηle.trans (by linarith)
  have hγle3η : γ ≤ 3 * η := by
    rw [hγ]
    rw [div_le_iff₀ hkR]
    have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [mul_nonneg hδ.le (sq_nonneg η)]
  have hγmass : γ ≤ dhjDensity (dhjCell B i) := by
    have hnum : δ * η ^ 2 ≤ 3 * η * (δ - 3 * η) := by
      nlinarith [mul_nonneg hδ.le (sq_nonneg η)]
    calc
      γ = δ * η ^ 2 / k := hγ
      _ ≤ (3 * η * (δ - 3 * η)) / k :=
        (div_le_div_iff_of_pos_right hkR).mpr hnum
      _ = (3 * η / k) * (δ - 3 * η) := by ring
      _ ≤ (3 * η / k) * dhjDensity Q := by gcongr
      _ ≤ dhjDensity (dhjCell B i) := hiMass
  refine ⟨D, fun j => dhj_cellFactor_insensitive B i j, ?_, ?_⟩
  · rwa [hmeet]
  · rw [hmeet]
    calc
      (δ + γ) * dhjDensity (dhjCell B i) ≤
          (δ + 3 * η) * dhjDensity (dhjCell B i) := by
        gcongr
        exact dhjDensity_nonneg _
      _ ≤ dhjDensity (B ∩ dhjCell B i) := hiCorr

private def dhjFlattenEquiv {L G : ℕ} {α : Type*} :
    (Fin L → Fin G → α) ≃ (Fin L × Fin G → α) where
  toFun := dhjFlattenBlocks
  invFun f i j := f (i, j)
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def dhjTheta (k m₀ : ℕ) (δ : ℝ) : ℝ :=
  δ / (4 * dhjLineCount k m₀)

private noncomputable def dhjEta (k m₀ : ℕ) (δ : ℝ) : ℝ :=
  δ * dhjTheta k m₀ δ / 48

private noncomputable def dhjGamma (k m₀ : ℕ) (δ : ℝ) : ℝ :=
  δ * dhjEta k m₀ δ ^ 2 / k

private theorem dhj_corollary11_blocks {k m₀ m : ℕ} {δ : ℝ}
    (hk : 2 ≤ k) (hm₀ : 0 < m₀) (hm₀m : m₀ ≤ m) (hkm : k ≤ m)
    (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hDHJ : dhjAt k m₀ (δ / 4))
    (hratio : ((k : ℝ) / (k + 1)) ^ m ≤ dhjEta k m₀ δ) :
    ∃ (G R : ℕ), 0 < G ∧
      ∀ A : Finset (Fin (R + 1) → Fin G → Fin (k + 1)),
        δ ≤ dhjDensity A →
        dhjLineFree
          (A.map (dhjFlattenEquiv (L := R + 1) (G := G)
            (α := Fin (k + 1))).toEmbedding) →
        ∃ (W : Combinatorics.Subspace (Fin m) (Fin (k + 1))
              (Fin (R + 1) × Fin G))
          (D : Fin k → Finset (Fin m → Fin (k + 1))),
          (∀ i, dhjInsensitive i (D i)) ∧
          dhjGamma k m₀ δ ≤ dhjDensity (dhjFamilyMeet D) ∧
          (δ + dhjGamma k m₀ δ) * dhjDensity (dhjFamilyMeet D) ≤
            dhjDensity (dhjPullback W
              (A.map (dhjFlattenEquiv (L := R + 1) (G := G)
                (α := Fin (k + 1))).toEmbedding) ∩ dhjFamilyMeet D) := by
  classical
  obtain ⟨hθpos, hθle, hηpos, hηlt, hηsq, hγpos, hγle⟩ :=
    dhj_constants hk hm₀ hδ hδle
  obtain ⟨G, R, hG, hregular⟩ :=
    dhj_lemma7_blocks (by omega) hm₀ hm₀m hδ
      (by positivity : 0 < dhjEta k m₀ δ ^ 2 / 2)
      hηsq hDHJ
  refine ⟨G, R, hG, ?_⟩
  intro A hA hlineFree
  obtain ⟨t, ht, p, V, hsections, hlines⟩ := hregular A hA
  obtain hhigh | hlow := dhj_lemma8_blocks (by omega) (hm₀.trans_le hm₀m)
    hηpos hθpos hηlt ht A p V hsections hlines
  · obtain ⟨y, hy⟩ := hhigh
    let W := dhjBlockFullSubspace p (dhjSubspaceMapConstants Fin.castSucc V) y
      (by omega : t + 1 ≤ R + 1)
    let B := dhjColumn
      (fun x : Fin m → Fin (k + 1) => dhjBlockSection A
        (dhjAppend p (dhjSubspaceMapConstants Fin.castSucc V x)) (by omega)) y
    let D : Fin k → Finset (Fin m → Fin (k + 1)) := fun _ => Finset.univ
    have hpull : dhjPullback W
        (A.map (dhjFlattenEquiv (L := R + 1) (G := G)
          (α := Fin (k + 1))).toEmbedding) = B := by
      exact dhjPullback_blockFullSubspace A p
        (dhjSubspaceMapConstants Fin.castSucc V) y (by omega)
    have hmeet : dhjFamilyMeet D = Finset.univ := dhj_familyMeet_univ
    refine ⟨W, D, ?_, ?_, ?_⟩
    · intro i
      exact dhjInsensitive_univ i
    · rw [hmeet, dhjDensity_univ]
      exact hγle.trans (hηsq.trans (by linarith))
    · rw [hmeet, dhjDensity_univ, mul_one, Finset.inter_univ, hpull]
      calc
        δ + dhjGamma k m₀ δ ≤ δ + dhjEta k m₀ δ ^ 2 / 2 :=
          by linarith
        _ ≤ dhjDensity B := by simpa [B] using hy
  · obtain ⟨y, hyden, hygood⟩ := hlow
    let W := dhjBlockFullSubspace p (dhjSubspaceMapConstants Fin.castSucc V) y
      (by omega : t + 1 ≤ R + 1)
    let B := dhjColumn
      (fun x : Fin m → Fin (k + 1) => dhjBlockSection A
        (dhjAppend p (dhjSubspaceMapConstants Fin.castSucc V x)) (by omega)) y
    have hpull : dhjPullback W
        (A.map (dhjFlattenEquiv (L := R + 1) (G := G)
          (α := Fin (k + 1))).toEmbedding) = B := by
      exact dhjPullback_blockFullSubspace A p
        (dhjSubspaceMapConstants Fin.castSucc V) y (by omega)
    have hBlineFree : dhjLineFree B := by
      rw [← hpull]
      exact dhjLineFree_pullback _ W hlineFree
    have hgood : dhjTheta k m₀ δ / 2 ≤ dhjDensity (dhjGoodRestrictedLines B) := by
      rw [← dhj_column_lineEvents_eq_goodLines A p V y ht]
      exact hygood
    obtain ⟨D, hDi, hDmass, hDcorr⟩ :=
      dhj_corollary11_cube (by omega) hkm hδ hδle hθpos hθle rfl rfl hratio B
        hBlineFree hyden hgood
    refine ⟨W, D, hDi, hDmass, ?_⟩
    rwa [hpull]

private def dhjBlockCore {k : ℕ} {J : Type*} (i : Fin k) {L : ℕ}
    (w : Fin L → J → Fin (k + 1)) : Fin L → J → Fin (k + 1) :=
  fun b => dhjReplaceLast i (w b)

private def dhjBlockInsensitive {k : ℕ} {J : Type*} (i : Fin k) {L : ℕ}
    (D : Finset (Fin L → J → Fin (k + 1))) : Prop :=
  ∀ w, w ∈ D ↔ dhjBlockCore i w ∈ D

private def dhjCurryEquiv {L : ℕ} {J α : Type*} :
    (Fin L → J → α) ≃ (Fin L × J → α) where
  toFun w q := w q.1 q.2
  invFun f b j := f (b, j)
  left_inv _ := rfl
  right_inv f := by
    funext q
    rcases q with ⟨b, j⟩
    rfl

private def dhjMiddleWord {X : Type*} {Q t : ℕ} (h : t + 1 ≤ Q)
    (p : Fin t → X) (z : X) (y : Fin (Q - (t + 1)) → X) : Fin Q → X :=
  fun q =>
    if hqt : q.val < t then p ⟨q.val, hqt⟩
    else if hqeq : q.val = t then z
    else y ⟨q.val - (t + 1), by omega⟩

private def dhjMiddleEquiv {X : Type*} {Q t : ℕ} (h : t + 1 ≤ Q) :
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

private noncomputable def dhjMiddleSection {X : Type*} [Fintype X] {Q t : ℕ}
    (R : Finset (Fin Q → X)) (h : t + 1 ≤ Q)
    (b : (Fin t → X) × (Fin (Q - (t + 1)) → X)) : Finset X := by
  classical
  exact Finset.univ.filter fun z => dhjMiddleWord h b.1 z b.2 ∈ R

private noncomputable def dhjProdSection {B X : Type*} [Fintype X]
    (A : Finset (B × X)) (b : B) : Finset X := by
  classical
  exact Finset.univ.filter fun x => (b, x) ∈ A

private def dhjJoinAt {X : Type*} {Q t : ℕ} (h : t ≤ Q)
    (p : Fin t → X) (y : Fin (Q - t) → X) : Fin Q → X :=
  fun q => if hqt : q.val < t then p ⟨q.val, hqt⟩
    else y ⟨q.val - t, by omega⟩

private def dhjTailCons {X : Type*} {Q t : ℕ} (h : t + 1 ≤ Q)
    (z : X) (y : Fin (Q - (t + 1)) → X) : Fin (Q - t) → X :=
  fun q => if hq : q.val = 0 then z else y ⟨q.val - 1, by omega⟩

private def dhjStageInsensitive {k Q t : ℕ} {J : Type*} (i : Fin k)
    (R : Finset (Fin Q → J → Fin (k + 1))) (h : t ≤ Q) : Prop :=
  ∀ (p : Fin t → J → Fin (k + 1))
    (y y' : Fin (Q - t) → J → Fin (k + 1)),
    dhjBlockCore i y = dhjBlockCore i y' →
      (dhjJoinAt h p y ∈ R ↔ dhjJoinAt h p y' ∈ R)

private def dhjBaseSuffixInsensitive {k Q t : ℕ} {J : Type*} (i : Fin k)
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1)))) : Prop :=
  ∀ (p : Fin t → J → Fin (k + 1))
    (y y' : Fin (Q - (t + 1)) → J → Fin (k + 1)),
    dhjBlockCore i y = dhjBlockCore i y' → ((p, y) ∈ S ↔ (p, y') ∈ S)

private noncomputable def dhjBatch {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    Finset (Fin Q → J → Fin (k + 1)) := by
  classical
  exact (S.product (dhjSubspacePoints V)).map (dhjMiddleEquiv h).symm.toEmbedding

private def dhjMiddleSubspace {k d Q t : ℕ} {J : Type*}
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

private noncomputable def dhjFlatBatch {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    Finset (Fin Q × J → Fin (k + 1)) := by
  classical
  exact (dhjBatch h S V).map
    (dhjCurryEquiv (L := Q) (J := J) (α := Fin (k + 1))).toEmbedding

private noncomputable def dhjFlatSet {k Q : ℕ} {J : Type*}
    (C : Finset (Fin Q → J → Fin (k + 1))) :
    Finset (Fin Q × J → Fin (k + 1)) := by
  classical
  exact C.map (dhjCurryEquiv (L := Q) (J := J) (α := Fin (k + 1))).toEmbedding

private noncomputable def dhjTileGain (k d : ℕ) {J : Type*}
    [Fintype J] [Fintype (J → Fin (k + 1))] (β : ℝ) : ℝ :=
  β / Fintype.card (Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) *
    (((k + 1 : ℕ) : ℝ) ^ d / Fintype.card (J → Fin (k + 1)))

private def dhjWordEquiv {I I' α : Type*} (e : I ≃ I') :
    (I → α) ≃ (I' → α) :=
  Equiv.arrowCongr e (Equiv.refl α)

private theorem dhjSubspacePoints_comp {k m d : ℕ} {I : Type*}
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I)
    (W : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)) :
    (dhjSubspacePoints W).map ⟨V, dhjSubspace_apply_injective V⟩ =
      dhjSubspacePoints (V.comp W) := by
  classical
  ext x
  simp [dhjSubspacePoints, Combinatorics.Subspace.comp_apply]

private theorem dhjTiled.map_subspace {k m d : ℕ} {I : Type*}
    [DecidableEq (Fin m → Fin (k + 1))]
    [DecidableEq (I → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I)
    {C : Finset (Fin m → Fin (k + 1))} (hC : dhjTiled d k C) :
    dhjTiled d k (C.map ⟨V, dhjSubspace_apply_injective V⟩) := by
  induction hC with
  | empty => simpa using (dhjTiled.empty :
      dhjTiled d k (∅ : Finset (I → Fin (k + 1))))
  | add C W hC hdis ih =>
      have hdis' : Disjoint
          (C.map ⟨V, dhjSubspace_apply_injective V⟩)
          (dhjSubspacePoints (V.comp W)) := by
        rw [← dhjSubspacePoints_comp V W]
        exact (Finset.disjoint_map _).mpr hdis
      have hadd := dhjTiled.add
        (C.map ⟨V, dhjSubspace_apply_injective V⟩) (V.comp W) ih hdis'
      rw [Finset.map_union, dhjSubspacePoints_comp V W]
      exact hadd

private theorem dhjDensity_map_subspace {k m : ℕ} {I : Type*}
    [Fintype (I → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I)
    (A : Finset (Fin m → Fin (k + 1))) :
    dhjDensity (A.map ⟨V, dhjSubspace_apply_injective V⟩) =
      dhjDensity A * dhjDensity (dhjSubspacePoints V) := by
  rw [dhjDensity, dhjDensity, dhjDensity_subspacePoints]
  simp only [Finset.card_map, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hbase : (0 : ℝ) < (k + 1 : ℕ) ^ m := by positivity
  field_simp

private theorem dhj_refine_one_tile {k m d : ℕ} {I : Type*}
    [Fintype I] [Fintype (I → Fin (k + 1))]
    (i : Fin k) {β : ℝ}
    (hSingle : ∀ (D : Finset (Fin m → Fin (k + 1))),
      dhjInsensitive i D →
        ∃ C : Finset (Fin m → Fin (k + 1)),
          C ⊆ D ∧ dhjTiled d k C ∧ dhjDensity (D \ C) < 2 * β)
    (E : Finset (I → Fin (k + 1))) (hE : dhjInsensitive i E)
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I) :
    ∃ B : Finset (I → Fin (k + 1)),
      B ⊆ dhjSubspacePoints V ∩ E ∧ dhjTiled d k B ∧
        dhjDensity ((dhjSubspacePoints V ∩ E) \ B) ≤
          2 * β * dhjDensity (dhjSubspacePoints V) := by
  classical
  let EV := dhjPullback V E
  have hEV : dhjInsensitive i EV := hE.pullback i E V
  obtain ⟨C, hCsub, hCtile, hCsmall⟩ := hSingle EV hEV
  let B := C.map ⟨V, dhjSubspace_apply_injective V⟩
  refine ⟨B, ?_, hCtile.map_subspace V, ?_⟩
  · intro x hx
    obtain ⟨z, hzC, rfl⟩ := Finset.mem_map.mp hx
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · exact (dhj_mem_subspacePoints V (V z)).mpr ⟨z, rfl⟩
    · exact (dhj_mem_pullback V E z).mp (hCsub hzC)
  · have hres : (dhjSubspacePoints V ∩ E) \ B =
        (EV \ C).map ⟨V, dhjSubspace_apply_injective V⟩ := by
      ext x
      constructor
      · intro hx
        have hx' := Finset.mem_sdiff.mp hx
        obtain ⟨z, hz⟩ := (dhj_mem_subspacePoints V x).mp
          (Finset.mem_inter.mp hx'.1).1
        subst x
        apply Finset.mem_map.mpr
        refine ⟨z, ?_, rfl⟩
        rw [Finset.mem_sdiff]
        refine ⟨(dhj_mem_pullback V E z).mpr (Finset.mem_inter.mp hx'.1).2, ?_⟩
        intro hzC
        exact hx'.2 (Finset.mem_map.mpr ⟨z, hzC, rfl⟩)
      · intro hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
        have hz' := Finset.mem_sdiff.mp hz
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_inter.mpr ⟨?_, (dhj_mem_pullback V E z).mp hz'.1⟩, ?_⟩
        · exact (dhj_mem_subspacePoints V (V z)).mpr ⟨z, rfl⟩
        · intro hzB
          obtain ⟨z', hz'C, hz'eq⟩ := Finset.mem_map.mp hzB
          exact hz'.2 ((dhjSubspace_apply_injective V hz'eq) ▸ hz'C)
    rw [hres, dhjDensity_map_subspace]
    have hpos : 0 < dhjDensity (dhjSubspacePoints V) := by
      rw [dhjDensity_subspacePoints]
      positivity
    exact (mul_lt_mul_of_pos_right hCsmall hpos).le

private theorem dhj_refine_tiled {k m d : ℕ} {I : Type*}
    [Fintype I] [Fintype (I → Fin (k + 1))]
    (i : Fin k) {β : ℝ}
    (hSingle : ∀ (D : Finset (Fin m → Fin (k + 1))),
      dhjInsensitive i D →
        ∃ C : Finset (Fin m → Fin (k + 1)),
          C ⊆ D ∧ dhjTiled d k C ∧ dhjDensity (D \ C) < 2 * β)
    (E : Finset (I → Fin (k + 1))) (hE : dhjInsensitive i E)
    {C : Finset (I → Fin (k + 1))} (hC : dhjTiled m k C) :
    ∃ B : Finset (I → Fin (k + 1)),
      B ⊆ C ∩ E ∧ dhjTiled d k B ∧
        dhjDensity ((C ∩ E) \ B) ≤ 2 * β * dhjDensity C := by
  induction hC with
  | empty =>
      refine ⟨∅, by simp, dhjTiled.empty, ?_⟩
      simp [dhjDensity_empty]
  | add C V hCtiled hdis ih =>
      obtain ⟨B₀, hB₀sub, hB₀tile, hB₀small⟩ := ih
      obtain ⟨Bᵥ, hBᵥsub, hBᵥtile, hBᵥsmall⟩ :=
        dhj_refine_one_tile i hSingle E hE V
      have hBdis : Disjoint B₀ Bᵥ := by
        rw [Finset.disjoint_left]
        intro x hx₀ hxᵥ
        exact (Finset.disjoint_left.mp hdis)
          (Finset.mem_inter.mp (hB₀sub hx₀)).1
          (Finset.mem_inter.mp (hBᵥsub hxᵥ)).1
      refine ⟨B₀ ∪ Bᵥ, ?_, dhjTiled_union hB₀tile hBᵥtile hBdis, ?_⟩
      · intro x hx
        refine Finset.mem_inter.mpr ⟨?_, ?_⟩
        · rcases Finset.mem_union.mp hx with hx₀ | hxᵥ
          · have hx' := Finset.mem_inter.mp (hB₀sub hx₀)
            exact Finset.mem_union_left _ hx'.1
          · have hx' := Finset.mem_inter.mp (hBᵥsub hxᵥ)
            exact Finset.mem_union_right _ hx'.1
        · rcases Finset.mem_union.mp hx with hx₀ | hxᵥ
          · exact (Finset.mem_inter.mp (hB₀sub hx₀)).2
          · exact (Finset.mem_inter.mp (hBᵥsub hxᵥ)).2
      · let R₀ := (C ∩ E) \ B₀
        let Rᵥ := (dhjSubspacePoints V ∩ E) \ Bᵥ
        have hres : ((C ∪ dhjSubspacePoints V) ∩ E) \ (B₀ ∪ Bᵥ) = R₀ ∪ Rᵥ := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union,
            not_or, R₀, Rᵥ]
          constructor
          · rintro ⟨⟨hxC | hxV, hxE⟩, hxB₀, hxBᵥ⟩
            · exact Or.inl ⟨⟨hxC, hxE⟩, hxB₀⟩
            · exact Or.inr ⟨⟨hxV, hxE⟩, hxBᵥ⟩
          · rintro (⟨⟨hxC, hxE⟩, hxB₀⟩ | ⟨⟨hxV, hxE⟩, hxBᵥ⟩)
            · refine ⟨⟨Or.inl hxC, hxE⟩, hxB₀, ?_⟩
              intro hxBᵥ
              exact (Finset.disjoint_left.mp hdis) hxC
                (Finset.mem_inter.mp (hBᵥsub hxBᵥ)).1
            · refine ⟨⟨Or.inr hxV, hxE⟩, ?_, hxBᵥ⟩
              intro hxB₀
              exact (Finset.disjoint_left.mp hdis)
                (Finset.mem_inter.mp (hB₀sub hxB₀)).1 hxV
        have hRdis : Disjoint R₀ Rᵥ := by
          rw [Finset.disjoint_left]
          intro x hx₀ hxᵥ
          exact (Finset.disjoint_left.mp hdis)
            (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx₀).1).1
            (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxᵥ).1).1
        rw [hres, dhjDensity_union R₀ Rᵥ hRdis,
          dhjDensity_union C (dhjSubspacePoints V) hdis]
        calc
          dhjDensity R₀ + dhjDensity Rᵥ ≤
              2 * β * dhjDensity C +
                2 * β * dhjDensity (dhjSubspacePoints V) :=
            add_le_add hB₀small hBᵥsmall
          _ = 2 * β *
              (dhjDensity C + dhjDensity (dhjSubspacePoints V)) := by ring

private noncomputable def dhjMeet {r k n : ℕ}
    (D : Fin r → Finset (Fin n → Fin (k + 1))) :
    Finset (Fin n → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun x => ∀ j, x ∈ D j

private def dhjIdentitySubspace (d k : ℕ) :
    Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin d) where
  idxFun := Sum.inr
  proper j := ⟨j, rfl⟩

private theorem dhj_exists_structured_tiling {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε) :
    ∀ r d : ℕ, 0 < d → ∀ β : ℝ, 0 < β → β ≤ 1 →
      ∃ n : ℕ, ∀ (a : Fin r → Fin k)
        (D : Fin r → Finset (Fin n → Fin (k + 1))),
        (∀ j, dhjInsensitive (a j) (D j)) →
          ∃ C : Finset (Fin n → Fin (k + 1)),
            C ⊆ dhjMeet D ∧ dhjTiled d k C ∧
              dhjDensity (dhjMeet D \ C) ≤ 2 * (r : ℝ) * β := by
  intro r
  induction r with
  | zero =>
      intro d hd β hβ hβle
      refine ⟨d, ?_⟩
      intro a D hD
      have hmeet : dhjMeet D = Finset.univ := by
        ext x
        simp
      have htile : dhjTiled d k
          (Finset.univ : Finset (Fin d → Fin (k + 1))) := by
        have hadd := dhjTiled.add
          (∅ : Finset (Fin d → Fin (k + 1))) (dhjIdentitySubspace d k)
          (dhjTiled.empty : dhjTiled d k
            (∅ : Finset (Fin d → Fin (k + 1))))
          (Finset.disjoint_empty_left _)
        simpa [dhjSubspacePoints_identity] using hadd
      refine ⟨Finset.univ, by simp [hmeet], htile, ?_⟩
      simp [hmeet, dhjDensity_empty]
  | succ r ih =>
      intro d hd β hβ hβle
      obtain ⟨m, hm, hSingle⟩ :=
        dhj_exists_tiling_insensitive_fin hk hd hβ hβle hDHJ
      obtain ⟨n, hOuter⟩ := ih m hm β hβ hβle
      refine ⟨n, ?_⟩
      intro a D hD
      let a₀ : Fin r → Fin k := fun j => a j.castSucc
      let D₀ : Fin r → Finset (Fin n → Fin (k + 1)) := fun j => D j.castSucc
      have hD₀ : ∀ j, dhjInsensitive (a₀ j) (D₀ j) := fun j => hD j.castSucc
      obtain ⟨C, hCsub, hCtile, hCsmall⟩ := hOuter a₀ D₀ hD₀
      let i := a (Fin.last r)
      let E := D (Fin.last r)
      have hE : dhjInsensitive i E := hD (Fin.last r)
      obtain ⟨B, hBsub, hBtile, hBsmall⟩ :=
        dhj_refine_tiled i (hSingle i) E hE hCtile
      have hmeet : dhjMeet D = dhjMeet D₀ ∩ E := by
        simpa [D₀, E] using dhjMeet_succ D
      refine ⟨B, ?_, hBtile, ?_⟩
      · intro x hx
        rw [hmeet]
        have hx' := Finset.mem_inter.mp (hBsub hx)
        exact Finset.mem_inter.mpr ⟨hCsub hx'.1, hx'.2⟩
      · let M := dhjMeet D₀ ∩ E
        let X := M \ C
        let Y := (C ∩ E) \ B
        have hres : dhjMeet D \ B = X ∪ Y := by
          rw [hmeet]
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, X, Y, M]
          constructor
          · rintro ⟨hxM, hxB⟩
            by_cases hxC : x ∈ C
            · exact Or.inr ⟨⟨hxC, hxM.2⟩, hxB⟩
            · exact Or.inl ⟨hxM, hxC⟩
          · rintro (⟨hxM, hxC⟩ | ⟨⟨hxC, hxE'⟩, hxB⟩)
            · refine ⟨hxM, ?_⟩
              intro hxB
              exact hxC (Finset.mem_inter.mp (hBsub hxB)).1
            · exact ⟨⟨hCsub hxC, hxE'⟩, hxB⟩
        have hXY : Disjoint X Y := by
          rw [Finset.disjoint_left]
          intro x hxX hxY
          exact (Finset.mem_sdiff.mp hxX).2
            (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxY).1).1
        have hXsub : X ⊆ dhjMeet D₀ \ C := by
          intro x hx
          have hx' := Finset.mem_sdiff.mp hx
          exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx'.1).1, hx'.2⟩
        have hXsmall : dhjDensity X ≤ 2 * (r : ℝ) * β :=
          (dhjDensity_mono hXsub).trans hCsmall
        have hYsmall : dhjDensity Y ≤ 2 * β := by
          calc
            dhjDensity Y ≤ 2 * β * dhjDensity C := hBsmall
            _ ≤ 2 * β * 1 := by
              exact mul_le_mul_of_nonneg_left (dhjDensity_le_one C) (by positivity)
            _ = 2 * β := by ring
        rw [hres, dhjDensity_union X Y hXY]
        calc
          dhjDensity X + dhjDensity Y ≤ 2 * (r : ℝ) * β + 2 * β :=
            add_le_add hXsmall hYsmall
          _ = 2 * ((r + 1 : ℕ) : ℝ) * β := by
            push_cast
            ring

private theorem dhj_inter_subspacePoints {k m : ℕ} {I : Type*}
    [DecidableEq (I → Fin (k + 1))]
    (A : Finset (I → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I) :
    A ∩ dhjSubspacePoints V =
      (dhjPullback V A).map ⟨V, dhjSubspace_apply_injective V⟩ := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := (dhj_mem_subspacePoints V x).mp
      (Finset.mem_inter.mp hx).2
    exact Finset.mem_map.mpr
      ⟨z, (dhj_mem_pullback V A z).mpr (Finset.mem_inter.mp hx).1, rfl⟩
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_inter.mpr
      ⟨(dhj_mem_pullback V A z).mp hz,
        (dhj_mem_subspacePoints V (V z)).mpr ⟨z, rfl⟩⟩

private theorem dhjDensity_inter_subspacePoints {k m : ℕ} {I : Type*}
    [Fintype (I → Fin (k + 1))] [DecidableEq (I → Fin (k + 1))]
    (A : Finset (I → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I) :
    dhjDensity (A ∩ dhjSubspacePoints V) =
      dhjDensityOn A V * dhjDensity (dhjSubspacePoints V) := by
  rw [dhj_inter_subspacePoints A V, dhjDensity_map_subspace]
  rfl

private theorem dhjTiled.exists_densityOn_ge {k d : ℕ} {I : Type*}
    [Fintype (I → Fin (k + 1))]
    [DecidableEq (I → Fin (k + 1))]
    {C : Finset (I → Fin (k + 1))} (hC : dhjTiled d k C)
    (A : Finset (I → Fin (k + 1))) {q : ℝ} (hCne : C.Nonempty)
    (havg : q * dhjDensity C ≤ dhjDensity (A ∩ C)) :
    ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) I,
      dhjSubspacePoints V ⊆ C ∧ q ≤ dhjDensityOn A V := by
  induction hC with
  | empty => simp at hCne
  | add C V hCtiled hdis ih =>
      by_cases hV : q ≤ dhjDensityOn A V
      · refine ⟨V, ?_, hV⟩
        exact Finset.subset_union_right
      · have hAdis : Disjoint (A ∩ C) (A ∩ dhjSubspacePoints V) := by
          rw [Finset.disjoint_left]
          intro x hxC hxV
          exact (Finset.disjoint_left.mp hdis)
            (Finset.mem_inter.mp hxC).2 (Finset.mem_inter.mp hxV).2
        have hAunion : A ∩ (C ∪ dhjSubspacePoints V) =
            (A ∩ C) ∪ (A ∩ dhjSubspacePoints V) := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_union]
          aesop
        have htotal : q *
              (dhjDensity C + dhjDensity (dhjSubspacePoints V)) ≤
            dhjDensity (A ∩ C) +
              dhjDensity (A ∩ dhjSubspacePoints V) := by
          rw [← dhjDensity_union C (dhjSubspacePoints V) hdis,
            ← dhjDensity_union (A ∩ C) (A ∩ dhjSubspacePoints V) hAdis,
            ← hAunion]
          exact havg
        have hVpos : 0 < dhjDensity (dhjSubspacePoints V) := by
          rw [dhjDensity_subspacePoints]
          positivity
        have hVsmall : dhjDensity (A ∩ dhjSubspacePoints V) <
            q * dhjDensity (dhjSubspacePoints V) := by
          rw [dhjDensity_inter_subspacePoints A V]
          exact mul_lt_mul_of_pos_right (lt_of_not_ge hV) hVpos
        have hprev : q * dhjDensity C < dhjDensity (A ∩ C) := by
          nlinarith
        have hCne' : C.Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty.mp h, dhjDensity_empty] at hprev
          simp [dhjDensity_empty] at hprev
        obtain ⟨W, hWsub, hWden⟩ := ih hCne' hprev.le
        exact ⟨W, hWsub.trans Finset.subset_union_left, hWden⟩

private def dhjPrefixSubspace {I J α : Type*} (x : I → α) :
    Combinatorics.Subspace J α (I ⊕ J) where
  idxFun
    | Sum.inl i => Sum.inl (x i)
    | Sum.inr j => Sum.inr j
  proper j := ⟨Sum.inr j, rfl⟩

private theorem dhj_exists_family_tiling {k d : ℕ} {β : ℝ}
    (hk : 2 ≤ k) (hd : 0 < d) (hβ : 0 < β) (hβle : β ≤ 1)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε) :
    ∃ n : ℕ, ∀ (D : Fin k → Finset (Fin n → Fin (k + 1))),
      (∀ i, dhjInsensitive i (D i)) →
        ∃ C : Finset (Fin n → Fin (k + 1)),
          C ⊆ dhjFamilyMeet D ∧ dhjTiled d k C ∧
            dhjDensity (dhjFamilyMeet D \ C) ≤ 2 * (k : ℝ) * β := by
  obtain ⟨n, hn⟩ := dhj_exists_structured_tiling hk hDHJ k d hd β hβ hβle
  refine ⟨n, ?_⟩
  intro D hD
  obtain ⟨C, hCsub, hCtile, hCsmall⟩ := hn (fun i => i) D hD
  rw [dhjMeet_eq_familyMeet] at hCsub hCsmall
  exact ⟨C, hCsub, hCtile, hCsmall⟩

private theorem dhj_dichotomy_blocks {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 →
      ∀ d : ℕ, 0 < d → ∃ G R : ℕ, 0 < G ∧
      ∀ A : Finset (Fin (R + 1) → Fin G → Fin (k + 1)),
        ρ ≤ dhjDensity A →
          let A' := A.map (dhjFlattenEquiv (L := R + 1) (G := G)
            (α := Fin (k + 1))).toEmbedding
          (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin (R + 1) × Fin G),
              dhjLineIn A' l) ∨
            ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1))
                (Fin (R + 1) × Fin G),
              ρ + γ / 2 ≤ dhjDensityOn A' V := by
  classical
  obtain ⟨N₀, hN₀⟩ := hDHJ (δ / 4) (by positivity)
  let m₀ := N₀ + 1
  have hm₀ : 0 < m₀ := by simp [m₀]
  have hAt : dhjAt k m₀ (δ / 4) := hN₀ m₀ (by simp [m₀])
  obtain ⟨hθpos, hθle, hηpos, hηlt, hηsq, hγpos, hγle⟩ :=
    dhj_constants hk hm₀ hδ hδle
  let γ := dhjGamma k m₀ δ
  let η := dhjEta k m₀ δ
  have hηleone : η ≤ 1 := by
    dsimp only [η]
    linarith
  have hηsqle : η ^ 2 ≤ η := by
    nlinarith [mul_nonneg hηpos.le (sub_nonneg.mpr hηleone)]
  have hγleone : γ ≤ 1 := by
    dsimp only [γ, η] at hγle ⊢
    nlinarith
  have hγsqhalf_lt_one : γ ^ 2 / 2 < 1 := by
    nlinarith [mul_nonneg hγpos.le (sub_nonneg.mpr hγleone)]
  have hγsqhalf_lt_gamma : γ ^ 2 / 2 < γ := by
    nlinarith [mul_nonneg hγpos.le (sub_nonneg.mpr hγleone)]
  let β := γ ^ 2 / (4 * (k : ℝ))
  have hβpos : 0 < β := by dsimp only [β]; positivity
  have hβle : β ≤ 1 := by
    dsimp only [β]
    rw [div_le_one (by positivity : (0 : ℝ) < 4 * k)]
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [sq_nonneg γ,
      mul_nonneg hγpos.le (sub_nonneg.mpr hγleone)]
  have herr : 2 * (k : ℝ) * β = γ ^ 2 / 2 := by
    dsimp only [β]
    field_simp
    ring
  refine ⟨γ, hγpos, ?_⟩
  intro ρ hδρ hρle
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hAtρ : dhjAt k m₀ (ρ / 4) := by
    intro A hA
    exact hAt A (by linarith)
  obtain ⟨hθρpos, hθρle, hηρpos, hηρlt, hηρsq, hγρpos, hγρle⟩ :=
    dhj_constants hk hm₀ hρ hρle
  let ηρ := dhjEta k m₀ ρ
  let γρ := dhjGamma k m₀ ρ
  have hθmono : dhjTheta k m₀ δ ≤ dhjTheta k m₀ ρ := by
    simp only [dhjTheta]
    gcongr
  have hηmono : η ≤ ηρ := by
    simp only [η, ηρ, dhjEta]
    gcongr
  have hγmono : γ ≤ γρ := by
    simp only [γ, γρ, dhjGamma]
    gcongr
  have hηρleone : ηρ ≤ 1 := by
    dsimp only [ηρ]
    linarith
  have hηρsqle : ηρ ^ 2 ≤ ηρ := by
    nlinarith [mul_nonneg hηρpos.le (sub_nonneg.mpr hηρleone)]
  have hγρleone : γρ ≤ 1 := by
    dsimp only [γρ, ηρ] at hγρle ⊢
    nlinarith
  have hγρsqhalf_lt : γρ ^ 2 / 2 < γρ := by
    nlinarith [mul_nonneg hγρpos.le (sub_nonneg.mpr hγρleone)]
  intro d hd
  obtain ⟨M₀, hkM₀, hratio⟩ :=
    dhj_exists_ratio_pow_le (by omega : 0 < k) hηpos
  let d' := max d (max M₀ m₀)
  have hd' : 0 < d' := hd.trans_le (le_max_left _ _)
  obtain ⟨m, hTile⟩ :=
    dhj_exists_family_tiling hk hd' hβpos hβle hDHJ
  let Dall : Fin k → Finset (Fin m → Fin (k + 1)) := fun _ => Finset.univ
  have hDall : ∀ i, dhjInsensitive i (Dall i) := fun i => dhjInsensitive_univ i
  obtain ⟨Call, hCallSub, hCallTile, hCallSmall⟩ := hTile Dall hDall
  have hmeetAll : dhjFamilyMeet Dall = Finset.univ := dhj_familyMeet_univ
  have hCallSmall' : dhjDensity (Finset.univ \ Call) ≤ γ ^ 2 / 2 := by
    rw [← herr, ← hmeetAll]
    exact hCallSmall
  have hCallNe : Call.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sdiff_empty,
      dhjDensity_univ] at hCallSmall'
    linarith
  have hd'm : d' ≤ m := hCallTile.dimension_le_of_nonempty hCallNe
  have hm₀m : m₀ ≤ m := by
    apply (le_max_right M₀ m₀).trans
    exact (le_max_right d (max M₀ m₀)).trans hd'm
  have hM₀m : M₀ ≤ m := by
    apply (le_max_left M₀ m₀).trans
    exact (le_max_right d (max M₀ m₀)).trans hd'm
  have hkm : k ≤ m := hkM₀.trans hM₀m
  have hratioM : ((k : ℝ) / (k + 1)) ^ m ≤ dhjEta k m₀ ρ :=
    (hratio m hM₀m).trans hηmono
  obtain ⟨G, R, hG, hCorr⟩ :=
    dhj_corollary11_blocks hk hm₀ hm₀m hkm hρ hρle hAtρ hratioM
  refine ⟨G, R, hG, ?_⟩
  intro A hA
  let A' := A.map (dhjFlattenEquiv (L := R + 1) (G := G)
    (α := Fin (k + 1))).toEmbedding
  by_cases hlineFree : dhjLineFree A'
  · right
    obtain ⟨W, D, hDi, hDmass, hDcorr⟩ := hCorr A hA hlineFree
    obtain ⟨C, hCsub, hCtile, hCsmall⟩ := hTile D hDi
    have hCsmall' : dhjDensity (dhjFamilyMeet D \ C) ≤ γ ^ 2 / 2 := by
      rw [← herr]
      exact hCsmall
    have hCsmallρ : dhjDensity (dhjFamilyMeet D \ C) ≤ γρ ^ 2 / 2 := by
      calc
        dhjDensity (dhjFamilyMeet D \ C) ≤ γ ^ 2 / 2 := hCsmall'
        _ ≤ γρ ^ 2 / 2 := by
          exact div_le_div_of_nonneg_right
            ((sq_le_sq₀ hγpos.le hγρpos.le).2 hγmono) (by norm_num)
    let B := dhjPullback W A'
    have hCcorr : (ρ + γρ / 2) * dhjDensity C ≤ dhjDensity (B ∩ C) := by
      exact dhj_correlation_after_tiling hρ hγρpos hCsub hDmass hCsmallρ hDcorr
    have hCne : C.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sdiff_empty] at hCsmallρ
      exact (not_le_of_gt hγρsqhalf_lt) (hDmass.trans hCsmallρ)
    obtain ⟨V, hVsub, hVden⟩ :=
      hCtile.exists_densityOn_ge B hCne hCcorr
    let Z := W.comp V
    have hd_d' : d ≤ d' := le_max_left d (max M₀ m₀)
    obtain ⟨U, hUden⟩ :=
      dhj_exists_subspace_density_ge hd_d' (dhjPullback Z A')
    refine ⟨Z.comp U, ?_⟩
    calc
      ρ + γ / 2 ≤ ρ + γρ / 2 := by linarith
      _ ≤ dhjDensityOn B V := hVden
      _ = dhjDensityOn A' Z := (dhjDensityOn_comp A' W V).symm
      _ = dhjDensity (dhjPullback Z A') := rfl
      _ ≤ dhjDensityOn (dhjPullback Z A') U := hUden
      _ = dhjDensityOn A' (Z.comp U) := (dhjDensityOn_comp A' Z U).symm
  · left
    simpa only [dhjLineFree, not_forall, Classical.not_not] using hlineFree

private theorem dhj_dichotomy_fin {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 →
      ∀ d : ℕ, 0 < d → ∃ N : ℕ, 0 < N ∧
      ∀ A : Finset (Fin N → Fin (k + 1)), ρ ≤ dhjDensity A →
        (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin N), dhjLineIn A l) ∨
          ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin N),
            ρ + γ / 2 ≤ dhjDensityOn A V := by
  classical
  obtain ⟨γ, hγ, hblocks⟩ := dhj_dichotomy_blocks hk hδ hδle hDHJ
  refine ⟨γ, hγ, ?_⟩
  intro ρ hδρ hρle d hd
  obtain ⟨G, R, hG, hblock⟩ := hblocks ρ hδρ hρle d hd
  let I := Fin (R + 1) × Fin G
  let N := Fintype.card I
  let e : I ≃ Fin N := Fintype.equivFin I
  let b := dhjFlattenEquiv (L := R + 1) (G := G) (α := Fin (k + 1))
  let w := dhjWordEquiv e ( α := Fin (k + 1))
  let f := b.trans w
  have hN : 0 < N := by
    apply Fintype.card_pos_iff.mpr
    let q : I := (⟨0, by omega⟩, ⟨0, hG⟩)
    exact ⟨q⟩
  refine ⟨N, hN, ?_⟩
  intro A hA
  let Ablock := A.map f.symm.toEmbedding
  have hAblock : ρ ≤ dhjDensity Ablock := by
    rw [dhjDensity_map_equiv]
    exact hA
  obtain hline | hinc := hblock Ablock hAblock
  · left
    obtain ⟨l, hl⟩ := hline
    refine ⟨l.reindex e, ?_⟩
    intro a
    have ha := hl a
    change l a ∈ Ablock.map b.toEmbedding at ha
    rw [dhj_mem_map_equiv] at ha
    dsimp only [Ablock] at ha
    rw [dhj_mem_map_equiv] at ha
    have heq : l.reindex e a = w (l a) := by
      funext q
      change l.reindex e a q = l a (e.symm q)
      exact Combinatorics.Line.reindex_apply l e a q
    rw [heq]
    simpa [f] using ha
  · right
    obtain ⟨V, hV⟩ := hinc
    let V' := V.reindex (Equiv.refl (Fin d))
      (Equiv.refl (Fin (k + 1))) e
    refine ⟨V', ?_⟩
    have hpull : dhjPullback V' A = dhjPullback V
        (Ablock.map b.toEmbedding) := by
      ext z
      simp only [dhj_mem_pullback]
      rw [dhj_mem_map_equiv]
      dsimp only [Ablock]
      rw [dhj_mem_map_equiv]
      change V' z ∈ A ↔ f (b.symm (V z)) ∈ A
      have hVapply : V' z = w (V z) := dhjSubspace_reindex_apply V e z
      rw [hVapply]
      rfl
    simpa [dhjDensityOn, hpull] using hV

private theorem dhjThreshold_succ {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε)
    {δ : ℝ} (hδ : 0 < δ) : dhjThreshold (k + 1) δ := by
  by_cases hδle : δ ≤ 1
  · obtain ⟨γ, hγ, hstep⟩ := dhj_dichotomy_fin hk hδ hδle hDHJ
    obtain ⟨r, hr⟩ := exists_nat_gt ((1 - δ) / (γ / 2))
    have hinc : 0 < γ / 2 := by positivity
    have htop : 1 < δ + (r : ℝ) * (γ / 2) := by
      have hmul := mul_lt_mul_of_pos_right hr hinc
      rw [div_mul_cancel₀ (1 - δ) hinc.ne'] at hmul
      linarith
    obtain ⟨N, hN, hAt⟩ :=
      dhj_iterate_dichotomy hδ hγ hstep r δ le_rfl htop
    exact dhjThreshold_of_at (by omega) hAt
  · refine ⟨1, ?_⟩
    intro n hn A hA
    have hAle : dhjDensity A ≤ 1 := dhjDensity_le_one A
    exfalso
    exact (not_le_of_gt (lt_of_not_ge hδle)) (hA.trans hAle)

private theorem dhjThreshold_add_two : ∀ t : ℕ, ∀ δ : ℝ, 0 < δ →
    dhjThreshold (t + 2) δ := by
  intro t
  induction t with
  | zero =>
      intro δ hδ
      simpa using dhjThreshold_two hδ
  | succ t ih =>
      intro δ hδ
      have h := dhjThreshold_succ (k := t + 2) (by omega)
        (fun ε hε => ih ε hε) hδ
      exact h

private theorem dhjThreshold_all (k : ℕ) (hk : 2 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    dhjThreshold k δ := by
  have h := dhjThreshold_add_two (k - 2) δ hδ
  convert h using 1
  omega

/--
For every `k ≥ 2` and `δ > 0` there is `N` such that every `A : Finset (Fin N → Fin k)` with `δ *
((k : ℝ) ^ N) ≤ (A.card : ℝ)` contains a combinatorial line `l : Combinatorics.Line (Fin k) (Fin
N)` with `l a ∈ A` for all `a`. Source: H. Furstenberg and Y. Katznelson, J. Anal. Math. 57 (1991)
and Hales-Jewett, Trans. AMS 106 (1963); Lean states finitary density form over `Fin N → Fin k`
with coloring version as corollary.

Proves `Wanted` entry `density_hales_jewett`.

Proof: We follow the density-increment route of Dodos–Kanellopoulos–Tyros, with the binary
case supplied by Sperner's theorem and the required Graham–Rothschild line theorem proved above.
-/
theorem density_hales_jewett :
    ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ,
      ∀ A : Finset (Fin N → Fin k),
        δ * ((k : ℝ) ^ N) ≤ (A.card : ℝ) →
          ∃ l : Combinatorics.Line (Fin k) (Fin N), ∀ a : Fin k, l a ∈ A := by
  intro k hk δ hδ
  obtain ⟨N, hN⟩ := dhjThreshold_all k hk δ hδ
  refine ⟨N, ?_⟩
  intro A hA
  have hden : δ ≤ dhjDensity A := by
    rw [dhjDensity]
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    rw [le_div_iff₀ (by positivity)]
    exact hA
  obtain ⟨l, hl⟩ := hN N le_rfl A hden
  exact ⟨l, hl⟩

end MathlibExt.Combinatorics.DensityHalesJewettWanted
