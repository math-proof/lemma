/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Fin
import Theorem.Combinatorics.Enumerative.PeakStatistic231


section

namespace MetaMathlibExt

namespace Peak231

def peakConv (F : ℕ → ℕ → ℕ) (a b k : ℕ) : ℕ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, F a p.1 * F b p.2

def peakRec (F : ℕ → ℕ → ℕ) (n k : ℕ) : ℕ :=
  ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
    (if q.1 = 0 ∨ q.2 = 0 then peakConv F q.1 q.2 k
     else (if k = 0 then 0 else peakConv F q.1 q.2 (k - 1)))

def peakV (n p : ℕ) : ℕ :=
  if n = 0 then 0 else 2 ^ (n - p - 1) * Nat.choose (n - 1) p

def peakT (n k : ℕ) : ℕ :=
  2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) * catalan k

def peakU : PowerSeries ℕ :=
  PowerSeries.mk fun m => if m = 0 then 0 else 2 ^ (m - 1)

-- N1
def joinMaxFun {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
    Fin (a + b + 1) → Fin (a + b + 1) :=
  fun i =>
    if h1 : i.val < a then ⟨(α ⟨i.val, h1⟩).val, by have h2 := (α ⟨i.val, h1⟩).isLt; omega⟩
    else if _h2 : i.val = a then Fin.last (a + b)
    else ⟨a + (β ⟨i.val - a - 1, by have h3 := i.isLt; omega⟩).val,
      by have h4 := (β ⟨i.val - a - 1, by have h3 := i.isLt; omega⟩).isLt
         have h3 := i.isLt; omega⟩

end Peak231
end MetaMathlibExt
end
