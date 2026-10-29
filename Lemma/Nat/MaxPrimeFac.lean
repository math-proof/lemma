import Mathlib.Tactic
import Initialize.Tactic.Attr.Basic
import Theorem.Data.Nat.MaxPrimeFac
open Nat


namespace Nat

/--
[maxPrimeFac_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean)
-/
@[path]
lemma maxPrimeFac_zero :
-- imply
  maxPrimeFac 0 = 0 := by
-- proof
  simp [maxPrimeFac]

end Nat

namespace Nat

/--
[maxPrimeFac_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean)
-/
@[path]
lemma maxPrimeFac_one :
-- imply
  maxPrimeFac 1 = 0 := by
-- proof
  simp [maxPrimeFac]

end Nat

namespace Nat

/--
[prime_maxPrimeFac_of_one_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean)
-/
@[path]
lemma prime_maxPrimeFac_of_one_lt
  (n : ℕ)
-- given
  (h : 1 < n) :
-- imply
  Nat.Prime (maxPrimeFac n) := by
-- proof
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr h
  obtain ⟨a, hmem, heq⟩ := Finset.exists_mem_eq_sup n.primeFactors hne id
  have hprime : a.Prime := (Nat.mem_primeFactors.mp hmem).1
  rw [maxPrimeFac, heq]
  exact hprime

end Nat

namespace Nat

/--
[maxPrimeFac_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean)
-/
@[path]
lemma maxPrimeFac_dvd
  {n : ℕ}
-- given
  (hn : n ≠ 1) :
-- imply
  maxPrimeFac n ∣ n := by
-- proof
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · have hlt : 1 < n := by omega
    obtain ⟨a, hmem, heq⟩ :=
      Finset.exists_mem_eq_sup n.primeFactors (Nat.nonempty_primeFactors.mpr hlt) id
    have hdvd : a ∣ n := (Nat.mem_primeFactors.mp hmem).2.1
    rw [maxPrimeFac, heq]
    exact hdvd

end Nat

namespace Nat

/--
[le_maxPrimeFac](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean)
-/
@[path]
lemma le_maxPrimeFac
  {n p : ℕ}
-- given
  (hn : n ≠ 0)
  (hp : p.Prime)
  (h_dvd : p ∣ n) :
-- imply
  p ≤ maxPrimeFac n := by
-- proof
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, h_dvd, hn⟩
  have hle : id p ≤ n.primeFactors.sup id := Finset.le_sup hmem
  simpa [maxPrimeFac] using hle

end Nat

namespace Nat

/--
[maxPrimeFac_eq_of_dvd_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean)
-/
@[path]
lemma maxPrimeFac_eq_of_dvd_of_le
  (n p : ℕ)
-- given
  (hn : 0 < n)
  (hp : p.Prime)
  (h_dvd : p ∣ n)
  (h_le : maxPrimeFac n ≤ p) :
-- imply
  maxPrimeFac n = p :=
-- proof
le_antisymm h_le (le_maxPrimeFac hn.ne' hp h_dvd)

end Nat

namespace Nat

/--
[Prime.maxPrimeFac_eq_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean)
-/
@[path]
lemma Prime.maxPrimeFac_eq_self
  {p : ℕ}
-- given
  (hp : p.Prime) :
-- imply
  maxPrimeFac p = p := by
-- proof
  apply maxPrimeFac_eq_of_dvd_of_le p p hp.pos hp (dvd_refl p)
  exact Nat.le_of_dvd hp.pos (maxPrimeFac_dvd hp.ne_one)

end Nat

namespace Nat

/--
[maxPrimeFac_eq_self_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean)
-/
@[path]
lemma maxPrimeFac_eq_self_iff
  {n : ℕ} :
-- imply
  maxPrimeFac n = n ↔ n = 0 ∨ n.Prime := by
-- proof
  constructor
  · intro h
    rcases eq_or_ne n 0 with rfl | hn0
    · exact Or.inl rfl
    · rcases eq_or_ne n 1 with rfl | hn1
      · exact absurd (h.symm.trans maxPrimeFac_one) (by decide)
      · have hlt : 1 < n := by omega
        exact Or.inr (h ▸ prime_maxPrimeFac_of_one_lt n hlt)
  · rintro (rfl | hn)
    · exact maxPrimeFac_zero
    · exact hn.maxPrimeFac_eq_self

end Nat

namespace Nat

/--
[maxPrimeFac_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean)
-/
@[path]
lemma maxPrimeFac_mul
  {m n : ℕ}
-- given
  (hm : m ≠ 0)
  (hn : n ≠ 0) :
-- imply
  maxPrimeFac (m * n) = max (maxPrimeFac m) (maxPrimeFac n) := by
-- proof
  obtain rfl | hm_lt : m = 1 ∨ 1 < m := by omega
  · simp only [one_mul, maxPrimeFac_one]
    exact (max_eq_right (Nat.zero_le _)).symm
  obtain rfl | hn_lt : n = 1 ∨ 1 < n := by omega
  · simp only [mul_one, maxPrimeFac_one]
    exact (max_eq_left (Nat.zero_le _)).symm
  have hmn_lt : 1 < m * n := Nat.one_lt_mul_iff.mpr
    ⟨zero_lt_of_lt hm_lt, zero_lt_of_lt hn_lt, Or.inl hm_lt⟩
  apply le_antisymm
  · have hp : Nat.Prime (maxPrimeFac (m * n)) :=
      prime_maxPrimeFac_of_one_lt (m * n) hmn_lt
    rcases hp.dvd_mul.mp (maxPrimeFac_dvd (ne_of_gt hmn_lt)) with hpm | hpn
    · exact (le_maxPrimeFac hm hp hpm).trans (le_max_left _ _)
    · exact (le_maxPrimeFac hn hp hpn).trans (le_max_right _ _)
  · apply max_le
    · have hp : Nat.Prime (maxPrimeFac m) := prime_maxPrimeFac_of_one_lt m hm_lt
      apply le_maxPrimeFac (mul_ne_zero hm hn) hp
      exact dvd_mul_of_dvd_left (maxPrimeFac_dvd (ne_of_gt hm_lt)) n
    · have hp : Nat.Prime (maxPrimeFac n) := prime_maxPrimeFac_of_one_lt n hn_lt
      apply le_maxPrimeFac (mul_ne_zero hm hn) hp
      exact dvd_mul_of_dvd_right (maxPrimeFac_dvd (ne_of_gt hn_lt)) m

end Nat

namespace Nat

/--
[maxPrimeFac_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean)
-/
@[path]
lemma maxPrimeFac_pow
  {k : ℕ}
  {n : ℕ}
-- given
  (hk : k ≠ 0) :
-- imply
  maxPrimeFac (n ^ k) = maxPrimeFac n :=
-- proof
  match k, hk with
  | k + 1, _ => by
    by_cases hn : n = 0
    · subst n
      simp
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, maxPrimeFac_mul (pow_ne_zero _ hn) hn, ih (by omega)]
      simp

end Nat

namespace Nat

/--
[maxPrimeFac_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean)
-/
@[path]
lemma maxPrimeFac_le
  {n : ℕ} :
-- imply
  maxPrimeFac n ≤ n := by
-- proof
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [maxPrimeFac_zero]
  rcases eq_or_ne n 1 with rfl | hn1
  · simp [maxPrimeFac_one]
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (maxPrimeFac_dvd hn1)

end Nat

namespace Nat

/--
[isLeast_maxPrimeFac](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean)
-/
@[path]
lemma isLeast_maxPrimeFac
  {n : ℕ}
-- given
  (hn : 1 < n) :
-- imply
  IsLeast (upperBounds {p : ℕ | p.Prime ∧ p ∣ n}) (maxPrimeFac n) := by
-- proof
  constructor
  · rintro p ⟨hp, h_dvd⟩
    exact le_maxPrimeFac (zero_lt_of_lt hn).ne' hp h_dvd
  · intro b hb
    exact hb ⟨prime_maxPrimeFac_of_one_lt n hn, maxPrimeFac_dvd (ne_of_gt hn)⟩

end Nat

namespace Nat

/--
[maxPrimeFac_eq_sSup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean)
-/
@[path]
lemma maxPrimeFac_eq_sSup
  {n : ℕ}
-- given
  (hn : 1 < n) :
-- imply
  maxPrimeFac n = sSup {p : ℕ | p.Prime ∧ p ∣ n} := by
-- proof
  have h_lub : IsLUB {p : ℕ | p.Prime ∧ p ∣ n} (maxPrimeFac n) :=
    isLeast_maxPrimeFac hn
  exact (h_lub.csSup_eq
    ⟨maxPrimeFac n, prime_maxPrimeFac_of_one_lt n hn,
      maxPrimeFac_dvd (ne_of_gt hn)⟩).symm

end Nat

namespace Nat

/--
[one_lt_maxPrimeFac_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean)
-/
@[path]
lemma one_lt_maxPrimeFac_iff
  {n : ℕ} :
-- imply
  1 < maxPrimeFac n ↔ 1 < n := by
-- proof
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · simp only [lt_one_iff] at hn
    simp [hn, maxPrimeFac_zero]
  · simp [maxPrimeFac_one]
  · simpa [hn] using (prime_maxPrimeFac_of_one_lt n hn).one_lt

end Nat


-- created on 2026-10-23
-- updated on 2026-10-29
