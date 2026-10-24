import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LucasLehmerAcceptableSeed
open MetaMathlibExt


namespace MetaMathlibExt

/--
[lucasLehmerSeed_card_X](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean)
-/
@[path]
private lemma lucasLehmerSeed_card_X (s₁ : ℤ) (q : ℕ) [NeZero q] :
  Fintype.card (lucasLehmerSeed_X s₁ q) = q ^ 2 := by
  change Fintype.card (ZMod q × ZMod q) = q ^ 2
  rw [Fintype.card_prod, ZMod.card, sq]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lucasLehmerSeed_card_units_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean)
-/
@[path]
private lemma lucasLehmerSeed_card_units_lt (s₁ : ℤ) (q : ℕ) [NeZero q]
  (hq : 1 < q) : Fintype.card (lucasLehmerSeed_X s₁ q)ˣ < q ^ 2 := by
  have : Fact (1 < q) := ⟨hq⟩
  convert! card_units_lt (lucasLehmerSeed_X s₁ q)
  rw [lucasLehmerSeed_card_X]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lucasLehmerSeed_two_lt_minFac](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean)
-/
@[path]
private lemma lucasLehmerSeed_two_lt_minFac (p' : ℕ) :
  2 < Nat.minFac (mersenne (p' + 2)) := by
  refine (Nat.minFac_prime (one_lt_mersenne.2 ?_).ne').two_le.lt_of_ne' ?_
  · omega
  · rw [Ne, Nat.minFac_eq_two_iff, mersenne, Nat.pow_succ']
    exact Nat.two_not_dvd_two_mul_sub_one (Nat.one_le_two_pow)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lucasLehmerSeed_legendre_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean)
-/
@[path]
private lemma lucasLehmerSeed_legendre_add_two (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
  (hjac : jacobiSym (s₁ + 2) q = -1) : legendreSym q (s₁ + 2) = -1 := by
  calc
    legendreSym q (s₁ + 2) = jacobiSym (s₁ + 2) q :=
      jacobiSym.legendreSym.to_jacobiSym q (s₁ + 2)
    _ = -1 := hjac

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lucasLehmerSeed_legendre_sub_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean)
-/
@[path]
private lemma lucasLehmerSeed_legendre_sub_two (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
  (hjac : jacobiSym (s₁ - 2) q = 1) : legendreSym q (s₁ - 2) = 1 := by
  calc
    legendreSym q (s₁ - 2) = jacobiSym (s₁ - 2) q :=
      jacobiSym.legendreSym.to_jacobiSym q (s₁ - 2)
    _ = 1 := hjac

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lucasLehmerSeed_legendre_D](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean)
-/
@[path]
private lemma lucasLehmerSeed_legendre_D (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
  (hplus : legendreSym q (s₁ + 2) = -1)
  (hminus : legendreSym q (s₁ - 2) = 1) :
  legendreSym q (s₁ ^ 2 - 4) = -1 := by
  rw [show s₁ ^ 2 - 4 = (s₁ + 2) * (s₁ - 2) by ring, legendreSym.mul, hplus, hminus]
  norm_num

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lucasLehmerSeed_delta_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean)
-/
@[path]
private lemma lucasLehmerSeed_delta_pow (s₁ : ℤ) (q i : ℕ) :
  lucasLehmerSeed_delta s₁ q ^ (2 * i + 1) =
    (lucasLehmerSeed_D s₁ q : lucasLehmerSeed_X s₁ q) ^ i *
      lucasLehmerSeed_delta s₁ q := by
  rw [pow_succ, pow_mul, lucasLehmerSeed_delta_sq]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lucasLehmerSeed_delta_pow_q](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean)
-/
@[path]
private lemma lucasLehmerSeed_delta_pow_q (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
  (hq_odd : Odd q) (hD : legendreSym q (s₁ ^ 2 - 4) = -1) :
  lucasLehmerSeed_delta s₁ q ^ q = -lucasLehmerSeed_delta s₁ q := by
  obtain ⟨k, rfl⟩ := hq_odd
  have hDpow : (lucasLehmerSeed_D s₁ (2 * k + 1)) ^ k = -1 := by
    have h := legendreSym.eq_pow (2 * k + 1) (s₁ ^ 2 - 4)
    rw [hD] at h
    have hhalf : (2 * k + 1) / 2 = k := by omega
    rw [hhalf] at h
    simpa [lucasLehmerSeed_D] using h.symm
  rw [lucasLehmerSeed_delta_pow]
  rw [← map_pow, hDpow, map_neg]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lucasLehmerSeed_coeZMod_pow_q](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean)
-/
@[path]
private lemma lucasLehmerSeed_coeZMod_pow_q (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
  (z : ZMod q) :
  (z : lucasLehmerSeed_X s₁ q) ^ q = (z : lucasLehmerSeed_X s₁ q) := by
  rw [← map_pow, ZMod.pow_card]

end MetaMathlibExt

/--
[acceptableSeed_of_jacobi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean)
-/
@[path]
private lemma acceptableSeed_of_jacobi_eq
  {n : ℕ}
  {s₁ : ℤ}
-- given
  (hn_odd : Odd n)
  (hn_ge : 3 ≤ n) :
-- imply
  jacobiSym (s₁ + 2) (mersenne n) = -1 ∧
    jacobiSym (s₁ - 2) (mersenne n) = 1 →
    (Nat.Prime (mersenne n) ↔
    (mersenne n : ℤ) ∣ Nat.iterate (fun x : ℤ => x ^ 2 - 2) (n - 2) s₁) := by
-- proof
  apply MetaMathlibExt.acceptableSeed_of_jacobi n hn_odd hn_ge s₁


-- created on 2026-10-20
-- updated on 2026-10-23
