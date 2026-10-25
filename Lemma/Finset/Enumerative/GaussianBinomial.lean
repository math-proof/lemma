import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.GaussianBinomial
open MathlibExt


namespace MathlibExt

/--
[gaussBinom_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
lemma gaussBinom_zero_right
  [Semiring R]
  {Q : R}
  {M : ℕ} :
-- imply
  gaussBinom Q M 0 = 1 := by
-- proof
  simp [gaussBinom]

end MathlibExt

namespace MathlibExt

/--
[gaussBinom_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
lemma gaussBinom_zero_succ
  [Semiring R]
  {Q : R}
  {k : ℕ} :
-- imply
  gaussBinom Q 0 (k + 1) = 0 := by
-- proof
  simp [gaussBinom]

end MathlibExt

namespace MathlibExt

/--
[gaussBinom_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
lemma gaussBinom_succ_succ
  [Semiring R]
  {Q : R}
  {M k : ℕ} :
-- imply
  gaussBinom Q (M + 1) (k + 1)
    = gaussBinom Q M k + Q ^ (k + 1) * gaussBinom Q M (k + 1) := by
-- proof
  simp [gaussBinom]

end MathlibExt

namespace MathlibExt

/--
[gaussBinom_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
lemma gaussBinom_eq_zero_of_lt
  [Semiring R]
  {Q : R}
  {M k : ℕ}
-- given
  (h : M < k) :
-- imply
  gaussBinom Q M k = 0 := by
-- proof
  induction M generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k => exact gaussBinom_zero_succ Q k
  | succ M ih =>
    cases k with
    | zero => omega
    | succ k =>
      rw [gaussBinom_succ_succ, ih k (by omega), ih (k + 1) (by omega)]
      simp

end MathlibExt

namespace MathlibExt

/--
[gaussBinom_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
lemma gaussBinom_self
  [Semiring R]
  {Q : R}
  {M : ℕ} :
-- imply
  gaussBinom Q M M = 1 := by
-- proof
  induction M with
  | zero => exact gaussBinom_zero_right Q 0
  | succ M ih =>
    rw [gaussBinom_succ_succ, ih,
      gaussBinom_eq_zero_of_lt Q M (M + 1) (Nat.lt_succ_self M)]
    simp

end MathlibExt

namespace MathlibExt

/--
[qPochFin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
lemma qPochFin_zero
  [CommRing R]
  {Q : R} :
-- imply
  qPochFin Q 0 = 1 := by
-- proof
  simp [qPochFin]

end MathlibExt

namespace MathlibExt

/--
[qPochFin_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
lemma qPochFin_succ
  [CommRing R]
  {Q : R}
  {m : ℕ} :
-- imply
  qPochFin Q (m + 1) = qPochFin Q m * (1 - Q ^ (m + 1)) := by
-- proof
  simp [qPochFin, Finset.prod_range_succ]

end MathlibExt

namespace MathlibExt

/--
[gaussBinom_mul_qPochFin_mul_qPochFin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean)
-/
@[path]
lemma gaussBinom_mul_qPochFin_mul_qPochFin
  [CommRing R]
  {Q : R}
  {M k : ℕ}
-- given
  (h : k ≤ M) :
-- imply
  gaussBinom Q M k * qPochFin Q k * qPochFin Q (M - k)
    = qPochFin Q M := by
-- proof
  induction M generalizing k with
  | zero =>
    have hk : k = 0 := by omega
    subst hk
    simp
  | succ M ih =>
    cases k with
    | zero =>
      simp
    | succ k =>
      by_cases hjk : k = M
      · rw [hjk]
        rw [gaussBinom_self]
        have hsub0 : M + 1 - (M + 1) = 0 := by omega
        rw [hsub0]
        simp
      · have h1 : k ≤ M := by omega
        have h2 : k + 1 ≤ M := by omega
        have hsub : M + 1 - (k + 1) = M - k := by omega
        rw [hsub, gaussBinom_succ_succ]
        have hPk : qPochFin Q (k + 1)
          = qPochFin Q k * (1 - Q ^ (k + 1)) :=
          qPochFin_succ Q k
        have hMj : M - k = (M - (k + 1)) + 1 := by omega
        have hMj' : (M - (k + 1)) + 1 = M - k := by omega
        have hPm : qPochFin Q (M - k)
          = qPochFin Q (M - (k + 1)) * (1 - Q ^ (M - k)) := by
          conv_lhs => rw [hMj]
          rw [qPochFin_succ, hMj']
        have hQ : Q ^ (M + 1) = Q ^ (k + 1) * Q ^ (M - k) := by
          rw [← pow_add]
          congr 1
          omega
        have ih1 := ih k h1
        have ih2 := ih (k + 1) h2
        have e1 : gaussBinom Q M k * qPochFin Q (k + 1)
          * qPochFin Q (M - k)
          = (1 - Q ^ (k + 1)) * qPochFin Q M := by
          rw [hPk]
          have hexp : gaussBinom Q M k
            * (qPochFin Q k * (1 - Q ^ (k + 1)))
            * qPochFin Q (M - k)
            = (1 - Q ^ (k + 1))
              * (gaussBinom Q M k * qPochFin Q k
                * qPochFin Q (M - k)) := by
            ring
          rw [hexp, ih1]
        have e2 : gaussBinom Q M (k + 1) * qPochFin Q (k + 1)
          * qPochFin Q (M - k)
          = (1 - Q ^ (M - k)) * qPochFin Q M := by
          rw [hPm]
          have hexp : gaussBinom Q M (k + 1) * qPochFin Q (k + 1)
            * (qPochFin Q (M - (k + 1)) * (1 - Q ^ (M - k)))
            = (1 - Q ^ (M - k))
              * (gaussBinom Q M (k + 1) * qPochFin Q (k + 1)
                * qPochFin Q (M - (k + 1))) := by
            ring
          rw [hexp, ih2]
        have hPM : qPochFin Q (M + 1)
          = qPochFin Q M * (1 - Q ^ (M + 1)) :=
          qPochFin_succ Q M
        have hexpand : (gaussBinom Q M k + Q ^ (k + 1)
          * gaussBinom Q M (k + 1)) * qPochFin Q (k + 1)
          * qPochFin Q (M - k)
          = gaussBinom Q M k * qPochFin Q (k + 1)
            * qPochFin Q (M - k)
            + Q ^ (k + 1) * (gaussBinom Q M (k + 1)
              * qPochFin Q (k + 1) * qPochFin Q (M - k)) := by
          ring
        rw [hexpand, e1, e2, hPM, hQ]
        ring
end MathlibExt



-- created on 2026-10-20
-- updated on 2026-10-23
