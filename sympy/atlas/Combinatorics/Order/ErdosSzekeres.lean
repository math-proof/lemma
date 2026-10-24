/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean -/

import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/-!
# Erdős–Szekeres monotone subsequence theorem

Every injective real sequence of length `(r - 1) * (s - 1) + 1` contains an
increasing subsequence of length `r` or a decreasing subsequence of length `s`.

Source: P. Erdős and G. Szekeres, “A combinatorial problem in geometry,”
_Compositio Mathematica_ 2 (1935), 463–470; the two-parameter
monotone-subsequence bound is proved on p. 468.
NUMDAM record: https://www.numdam.org/item/CM_1935__2__463_0/.
-/

/-- `k - 1 < k` for positive `k`. -/
theorem sub_one_lt_of_pos {k : ℕ} (hk : 0 < k) : k - 1 < k := by omega

/-- An increasing subsequence of `f` of length `k`: index- and value-strict. -/
def IsIncrSubseq {N : ℕ} (f : Fin N → ℝ) (k : ℕ) (φ : Fin k → Fin N) : Prop :=
  (∀ i j : Fin k, i < j → φ i < φ j) ∧
  (∀ i j : Fin k, i < j → f (φ i) < f (φ j))

/-- A decreasing subsequence of `f` of length `k`: index-strict, values strictly
decrease. -/
def IsDecrSubseq {N : ℕ} (f : Fin N → ℝ) (k : ℕ) (φ : Fin k → Fin N) : Prop :=
  (∀ i j : Fin k, i < j → φ i < φ j) ∧
  (∀ i j : Fin k, i < j → f (φ j) < f (φ i))

/-- There is an increasing subsequence of length `k` ending exactly at `p`. -/
def IsIncrEnd {N : ℕ} (f : Fin N → ℝ) (p : Fin N) (k : ℕ) : Prop :=
  ∃ (hk : 0 < k) (φ : Fin k → Fin N),
    IsIncrSubseq f k φ ∧ φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = p

/-- There is a decreasing subsequence of length `k` ending exactly at `p`. -/
def IsDecrEnd {N : ℕ} (f : Fin N → ℝ) (p : Fin N) (k : ℕ) : Prop :=
  ∃ (hk : 0 < k) (φ : Fin k → Fin N),
    IsDecrSubseq f k φ ∧ φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = p

/-- Classical decidability for filtering positions by `IsIncrEnd`. -/
noncomputable instance decIncrEnd (N : ℕ) (f : Fin N → ℝ) (p : Fin N) :
    DecidablePred (IsIncrEnd f p) :=
  fun _ => Classical.propDecidable _

/-- Classical decidability for filtering positions by `IsDecrEnd`. -/
noncomputable instance decDecrEnd (N : ℕ) (f : Fin N → ℝ) (p : Fin N) :
    DecidablePred (IsDecrEnd f p) :=
  fun _ => Classical.propDecidable _

/-- No strict pair exists in `Fin 1`. -/
theorem fin1_false {i j : Fin 1} (hij : i < j) : False := by
  have hiv : i.val < j.val := Fin.lt_def.mp hij
  have h1 := i.isLt
  have h2 := j.isLt
  omega

/-- Singletons are increasing subsequences. -/
theorem singleton_incr {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    IsIncrSubseq f 1 (fun _ => p) :=
  ⟨fun _ _ hij => False.elim (fin1_false hij),
    fun _ _ hij => False.elim (fin1_false hij)⟩

/-- Singletons are decreasing subsequences. -/
theorem singleton_decr {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    IsDecrSubseq f 1 (fun _ => p) :=
  ⟨fun _ _ hij => False.elim (fin1_false hij),
    fun _ _ hij => False.elim (fin1_false hij)⟩

/-- Length of the longest increasing subsequence ending at `p`. -/
noncomputable def incrLen {N : ℕ} (f : Fin N → ℝ) (p : Fin N) : ℕ :=
  ((Finset.range (N + 1)).filter (IsIncrEnd f p)).max'
    ⟨1, by
      have hN : 0 < N := by
        have h := p.isLt
        omega
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, fun _ => p, singleton_incr f p, rfl⟩⟩

/-- Length of the longest decreasing subsequence ending at `p`. -/
noncomputable def decrLen {N : ℕ} (f : Fin N → ℝ) (p : Fin N) : ℕ :=
  ((Finset.range (N + 1)).filter (IsDecrEnd f p)).max'
    ⟨1, by
      have hN : 0 < N := by
        have h := p.isLt
        omega
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, fun _ => p, singleton_decr f p, rfl⟩⟩

/-- Append `p` to a length-`k` map, yielding a length-`k+1` map. -/
def extendMap {N k : ℕ} (φ : Fin k → Fin N) (p : Fin N) : Fin (k + 1) → Fin N :=
  fun i => if h : i.val < k then φ ⟨i.val, h⟩ else p
end MathlibExt.Combinatorics.Order.ErdosSzekeres
