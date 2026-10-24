import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RoughNumbers
open Nat


namespace Nat

/--
[isRough_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
lemma isRough_iff
  {n k : ℕ} :
-- imply
  n.IsRough k ↔ n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → k < p :=
-- proof
  Iff.rfl

end Nat

namespace Nat

/--
[IsRough.ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
lemma IsRough.ne_zero
  {n k : ℕ}
-- given
  (h : n.IsRough k) :
-- imply
  n ≠ 0 :=
-- proof
  h.1

end Nat

namespace Nat

/--
[IsRough.pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
lemma IsRough.pos
  {n k : ℕ}
-- given
  (h : n.IsRough k) :
-- imply
  0 < n :=
-- proof
  Nat.pos_of_ne_zero h.ne_zero

end Nat

namespace Nat

/--
[IsRough.lt_of_prime_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
lemma IsRough.lt_of_prime_dvd
  {n k p : ℕ}
-- given
  (h : n.IsRough k)
  (hp : p.Prime)
  (hdvd : p ∣ n) :
-- imply
  k < p :=
-- proof
  h.2 p hp hdvd

end Nat

namespace Nat

/--
[isRough_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
lemma isRough_one
  {k : ℕ} :
-- imply
  (1 : ℕ).IsRough k :=
-- proof
  ⟨one_ne_zero, fun _ hp hdvd => (hp.ne_one (Nat.dvd_one.mp hdvd)).elim⟩

end Nat

namespace Nat

/--
[Prime.isRough_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
lemma Prime.isRough_iff
  {p k : ℕ}
-- given
  (hp : p.Prime) :
-- imply
  p.IsRough k ↔ k < p := by
-- proof
  constructor
  · intro h
    exact h.lt_of_prime_dvd hp dvd_rfl
  · intro hk
    refine ⟨hp.ne_zero, fun q hq hdvd => ?_⟩
    have heq : q = p := (prime_dvd_prime_iff_eq hq hp).mp hdvd
    rwa [heq]

end Nat

namespace Nat

/--
[IsRough.of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
lemma IsRough.of_dvd
  {m d k : ℕ}
-- given
  (h : m.IsRough k)
  (hdvd : d ∣ m)
  (hd : d ≠ 0) :
-- imply
  d.IsRough k :=
-- proof
  ⟨hd, fun _ hp hpd => h.lt_of_prime_dvd hp (hpd.trans hdvd)⟩

end Nat

namespace Nat

/--
[isRough_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
lemma isRough_mul
  {m n k : ℕ} :
-- imply
  (m * n).IsRough k ↔ m.IsRough k ∧ n.IsRough k := by
-- proof
  constructor
  · intro h
    refine ⟨h.of_dvd (Nat.dvd_mul_right m n) ?_,
      h.of_dvd (Nat.dvd_mul_left n m) ?_⟩
    · intro hm
      exact h.ne_zero (by rw [hm, zero_mul])
    · intro hn
      exact h.ne_zero (by rw [hn, mul_zero])
  · rintro ⟨hm, hn⟩
    refine ⟨mul_ne_zero hm.ne_zero hn.ne_zero, fun _ hp hdvd => ?_⟩
    rw [hp.dvd_mul] at hdvd
    exact hdvd.elim (hm.lt_of_prime_dvd hp) (hn.lt_of_prime_dvd hp)

end Nat

namespace Nat

/--
[IsRough.mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
lemma IsRough.mul
  {m n k : ℕ}
-- given
  (hm : m.IsRough k)
  (hn : n.IsRough k) :
-- imply
  (m * n).IsRough k :=
-- proof
  isRough_mul.mpr ⟨hm, hn⟩

end Nat

namespace Nat

/--
[IsRough.of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
lemma IsRough.of_le
  {n k l : ℕ}
-- given
  (h : n.IsRough k)
  (hle : l ≤ k) :
-- imply
  n.IsRough l :=
-- proof
  ⟨h.ne_zero, fun _ hp hdvd => lt_of_le_of_lt hle (h.lt_of_prime_dvd hp hdvd)⟩

end Nat

namespace Nat

/--
[IsRough.eq_one_of_mem_smoothNumbers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
lemma IsRough.eq_one_of_mem_smoothNumbers
  {n k : ℕ}
-- given
  (hrough : n.IsRough k)
  (hsmooth : n ∈ smoothNumbers (k + 1)) :
-- imply
  n = 1 := by
-- proof
  by_contra hn1
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
  have hlt1 : k < p := hrough.lt_of_prime_dvd hp hpdvd
  rw [Nat.mem_smoothNumbers] at hsmooth
  have hmem : p ∈ Nat.primeFactorsList n :=
    (Nat.mem_primeFactorsList hrough.ne_zero).mpr ⟨hp, hpdvd⟩
  have hlt2 : p < k + 1 := hsmooth.2 p hmem
  omega

end Nat

namespace Nat

/--
[IsRough.mem_roughNumbersUpTo](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
lemma IsRough.mem_roughNumbersUpTo
  {n N k : ℕ}
-- given
  (h : n.IsRough k)
  (hle : n ≤ N)
  (hn1 : n ≠ 1) :
-- imply
  n ∈ roughNumbersUpTo N (k + 1) := by
-- proof
  rw [roughNumbersUpTo, Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, h.ne_zero, ?_⟩
  intro hsmooth
  exact hn1 (h.eq_one_of_mem_smoothNumbers hsmooth)

end Nat

/--
[isRough_iff_primeFactorsList](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
private lemma isRough_iff_primeFactorsList_eq
  {n k : ℕ} :
-- imply
  n.IsRough k ↔ n ≠ 0 ∧ ∀ p ∈ primeFactorsList n, k < p := by
-- proof
  apply Nat.isRough_iff_primeFactorsList


-- created on 2026-10-20
-- updated on 2026-10-23
