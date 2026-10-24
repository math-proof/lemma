/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

section
open scoped BigOperators
namespace MetaMathlibExt
private abbrev binomialTMotzkinStep (t : ℕ) := Σ k : Fin (t + 1), Fin (Nat.choose t k)
private abbrev binomialTMotzkinHeight (t : ℕ) : binomialTMotzkinStep t → ℤ :=
  fun s => 1 - (s.1 : ℤ)
private noncomputable def binomialTMotzkinCount (t n : ℕ) (h : ℤ) : ℕ :=
  Fintype.card {p : Fin n → binomialTMotzkinStep t //
    (∀ m : Fin (n + 1),
      0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0) ∧
    ∑ i : Fin n, binomialTMotzkinHeight t (p i) = h}

private theorem snoc_total (t n : ℕ) (q : Fin n → binomialTMotzkinStep t)
    (s : binomialTMotzkinStep t) :
    ∑ i : Fin (n + 1), binomialTMotzkinHeight t
        (Fin.snoc (α := fun _ => binomialTMotzkinStep t) q s i)
      = (∑ i : Fin n, binomialTMotzkinHeight t (q i)) + binomialTMotzkinHeight t s := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

private theorem snoc_prefix_castSucc (t n : ℕ) (q : Fin n → binomialTMotzkinStep t)
    (s : binomialTMotzkinStep t) (m' : Fin (n + 1)) :
    (∑ i : Fin (n + 1), if i.1 < (Fin.castSucc m').1
      then binomialTMotzkinHeight t (Fin.snoc (α := fun _ => binomialTMotzkinStep t) q s i) else 0)
      = ∑ i : Fin n, if i.1 < m'.1 then binomialTMotzkinHeight t (q i) else 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.snoc_castSucc, Fin.val_last]
  have hle : m'.val ≤ n := Nat.le_of_lt_succ m'.isLt
  rw [ite_eq_right (by omega)]
  simp

private theorem snoc_prefix_last (t n : ℕ) (q : Fin n → binomialTMotzkinStep t)
    (s : binomialTMotzkinStep t) :
    (∑ i : Fin (n + 1), if i.1 < (Fin.last (n + 1)).1
      then binomialTMotzkinHeight t (Fin.snoc (α := fun _ => binomialTMotzkinStep t) q s i) else 0)
      = ∑ i : Fin (n + 1), binomialTMotzkinHeight t
          (Fin.snoc (α := fun _ => binomialTMotzkinStep t) q s i) := by
  rw [Fin.val_last]
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.1 < n + 1 := i.isLt
  rw [ite_eq_left hi]

private theorem snoc_pred_iff (t n : ℕ) (h : ℤ) (hh : 0 ≤ h)
    (q : Fin n → binomialTMotzkinStep t) (s : binomialTMotzkinStep t) :
    ((∀ m : Fin (n + 1 + 1),
        0 ≤ ∑ i : Fin (n + 1), if i.1 < m.1
          then binomialTMotzkinHeight t (Fin.snoc (α := fun _ => binomialTMotzkinStep t) q s i) else
              0)
      ∧ ∑ i : Fin (n + 1), binomialTMotzkinHeight t
          (Fin.snoc (α := fun _ => binomialTMotzkinStep t) q s i) = h)
    ↔ ((∀ m' : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m'.1 then binomialTMotzkinHeight t (q i) else 0)
      ∧ ∑ i : Fin n, binomialTMotzkinHeight t (q i) = h - binomialTMotzkinHeight t s) := by
  rw [Fin.forall_fin_succ']
  constructor
  · rintro ⟨⟨hpref, hlast⟩, htot⟩
    rw [snoc_total] at htot
    refine ⟨?_, by omega⟩
    intro m'
    have h2 := hpref m'
    rwa [snoc_prefix_castSucc] at h2
  · rintro ⟨hpref, htot⟩
    have htot' : ∑ i : Fin (n + 1),
        binomialTMotzkinHeight t (Fin.snoc (α := fun _ => binomialTMotzkinStep t) q s i) = h := by
      rw [snoc_total]
      omega
    refine ⟨⟨?_, ?_⟩, htot'⟩
    · intro m'
      have h2 := hpref m'
      rwa [snoc_prefix_castSucc]
    · rw [snoc_prefix_last, htot']
      exact hh

private theorem pred_iff_symm (t n : ℕ) (h : ℤ) (hh : 0 ≤ h)
    (p : Fin (n + 1) → binomialTMotzkinStep t) :
    ((∀ m : Fin (n + 1 + 1),
        0 ≤ ∑ i : Fin (n + 1), if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0)
      ∧ ∑ i : Fin (n + 1), binomialTMotzkinHeight t (p i) = h)
    ↔ ((∀ m : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m.1
          then binomialTMotzkinHeight t (((Fin.snocEquiv (fun _ => binomialTMotzkinStep t)).symm
              p).2 i) else 0)
      ∧ ∑ i : Fin n, binomialTMotzkinHeight t
          (((Fin.snocEquiv (fun _ => binomialTMotzkinStep t)).symm p).2 i)
        = h - binomialTMotzkinHeight t (((Fin.snocEquiv (fun _ => binomialTMotzkinStep t)).symm
            p).1)) := by
  have h1 : ((∀ m : Fin (n + 1 + 1),
        0 ≤ ∑ i : Fin (n + 1), if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0)
      ∧ ∑ i : Fin (n + 1), binomialTMotzkinHeight t (p i) = h)
      ↔ ((∀ m : Fin (n + 1 + 1),
        0 ≤ ∑ i : Fin (n + 1), if i.1 < m.1
          then binomialTMotzkinHeight t (Fin.snoc (α := fun _ => binomialTMotzkinStep t)
              (Fin.init p) (p (Fin.last n)) i) else 0)
      ∧ ∑ i : Fin (n + 1), binomialTMotzkinHeight t
          (Fin.snoc (α := fun _ => binomialTMotzkinStep t) (Fin.init p) (p (Fin.last n)) i) =
              h) := by
    rw [Fin.snoc_init_self p]
  have h2 := snoc_pred_iff t n h hh (Fin.init p) (p (Fin.last n))
  exact h1.trans h2

private def baseEquiv (t n : ℕ) (h : ℤ) (hh : 0 ≤ h) :
    {p : Fin (n + 1) → binomialTMotzkinStep t //
      (∀ m : Fin (n + 1 + 1),
        0 ≤ ∑ i : Fin (n + 1), if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0)
        ∧ ∑ i : Fin (n + 1), binomialTMotzkinHeight t (p i) = h}
    ≃ {y : binomialTMotzkinStep t × (Fin n → binomialTMotzkinStep t) //
      (∀ m : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (y.2 i) else 0)
        ∧ ∑ i : Fin n, binomialTMotzkinHeight t (y.2 i) = h - binomialTMotzkinHeight t y.1} :=
  Equiv.subtypeEquiv (Fin.snocEquiv (fun _ => binomialTMotzkinStep t)).symm
    (fun p => pred_iff_symm t n h hh p)

private def repackEquiv (t n : ℕ) (h : ℤ) :
    {y : binomialTMotzkinStep t × (Fin n → binomialTMotzkinStep t) //
      (∀ m : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (y.2 i) else 0)
        ∧ ∑ i : Fin n, binomialTMotzkinHeight t (y.2 i) = h - binomialTMotzkinHeight t y.1}
    ≃ Σ s : binomialTMotzkinStep t, {q : Fin n → binomialTMotzkinStep t //
      (∀ m : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (q i) else 0)
        ∧ ∑ i : Fin n, binomialTMotzkinHeight t (q i) = h - binomialTMotzkinHeight t s} where
  toFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
  invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

private noncomputable def binomialTMotzkinDeficitPoly (t N : ℕ) : Polynomial ℚ :=
  (1 + Polynomial.X) ^ (t * N) - Polynomial.C (t : ℚ) * Polynomial.X * (1 + Polynomial.X) ^
      (t * N - 1)

private noncomputable abbrev binomialTMotzkinPS (t : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => ((((binomialTMotzkinCount t n 0 : ℕ))) : ℚ))
end MetaMathlibExt
end
