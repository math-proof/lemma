import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.AlgebraicGeometry.EllipticCurve.ManinSequence
open Int
open MathlibExt.AlgebraicGeometry.EllipticCurve
open ManinDegreeData


namespace Int

/--
[eq_quadratic_of_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinSequence.lean)
-/
@[path]
lemma eq_quadratic_of_recurrence
  {d : ℤ → ℤ}
  {q N n : ℤ}
-- given
  (hrec : ∀ n, d (n - 1) + d (n + 1) = 2 * d n + 2)
  (hzero : d 0 = q)
  (hnegOne : d (-1) = N) :
-- imply
  d n = n ^ 2 + (q + 1 - N) * n + q := by
-- proof
  let p : ℤ → ℤ := fun m ↦ m ^ 2 + (q + 1 - N) * m + q
  have hp (m : ℤ) : p (m - 1) + p (m + 1) = 2 * p m + 2 := by
    simp only [p]
    ring
  have hpzero : p 0 = q := by
    simp [p]
  have hpnegOne : p (-1) = N := by
    simp [p]
    ring
  have hpair : ∀ m : ℤ, d m = p m ∧ d (m - 1) = p (m - 1) := by
    intro m
    refine Int.inductionOn' m 0 ?_ ?_ ?_
    · exact ⟨hzero.trans hpzero.symm, by simpa using hnegOne.trans hpnegOne.symm⟩
    · intro k _ hk
      refine ⟨?_, ?_⟩
      · linarith [hrec k, hp k]
      · simpa only [add_sub_cancel_right] using hk.1
    · intro k _ hk
      refine ⟨hk.2, ?_⟩
      have hd := hrec (k - 1)
      have hpd := hp (k - 1)
      rw [show k - 1 + 1 = k by ring] at hd hpd
      linarith
  exact (hpair n).1

end Int

namespace Int

/--
[sq_le_four_mul_of_quadratic_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinSequence.lean)
-/
@[path]
lemma sq_le_four_mul_of_quadratic_nonnegative
  {a q : ℤ}
-- given
  (hnonneg : ∀ n : ℤ, 0 ≤ n ^ 2 + a * n + q)
  (hnotTwoZeros : ∀ n : ℤ, n ^ 2 + a * n + q = 0 → (n + 1) ^ 2 + a * (n + 1) + q = 0 → False) :
-- imply
  a ^ 2 ≤ 4 * q := by
-- proof
  by_contra hle
  have hbad : 4 * q < a ^ 2 := lt_of_not_ge hle
  obtain ha | ha := Int.even_or_odd a
  · obtain ⟨k, hk⟩ := ha
    have h := hnonneg (-k)
    rw [hk] at hbad h
    nlinarith
  · obtain ⟨k, hk⟩ := ha
    have hleft := hnonneg (-k - 1)
    have hright := hnonneg (-k)
    have hzleft : (-k - 1) ^ 2 + a * (-k - 1) + q = 0 := by
      rw [hk] at hbad hleft hright ⊢
      nlinarith
    have hzright : (-k) ^ 2 + a * (-k) + q = 0 := by
      rw [hk] at hbad hleft hright ⊢
      nlinarith
    apply hnotTwoZeros (-k - 1) hzleft
    convert hzright using 1
    ring
end Int
namespace MathlibExt.AlgebraicGeometry.EllipticCurve


namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData

/--
[hasse_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinSequence.lean)
-/
@[path]
lemma hasse_bound
  {q N : ℕ}
  {data : ManinDegreeData q N} :
-- imply
  (((q : ℤ) + 1 - (N : ℤ)) ^ 2 ≤ 4 * (q : ℤ)) := by
-- proof
  let dInt : ℤ → ℤ := fun n ↦ data.d n
  have hrec : ∀ n, dInt (n - 1) + dInt (n + 1) = 2 * dInt n + 2 := by
    intro n
    dsimp only [dInt]
    exact_mod_cast data.recurrence n
  have hzero : dInt 0 = q := by
    dsimp only [dInt]
    exact_mod_cast data.zero
  have hnegOne : dInt (-1) = N := by
    dsimp only [dInt]
    exact_mod_cast data.negOne
  have hquadratic (n : ℤ) :
    dInt n = n ^ 2 + ((q : ℤ) + 1 - (N : ℤ)) * n + q :=
    Int.eq_quadratic_of_recurrence dInt q N hrec hzero hnegOne n
  apply Int.sq_le_four_mul_of_quadratic_nonnegative
  · intro n
    rw [← hquadratic]
    exact Int.natCast_nonneg _
  · intro n hn hn1
    apply data.noAdjacentZeros n
    · apply Int.ofNat_injective
      simpa [dInt, hquadratic n] using hn
    · apply Int.ofNat_injective
      simpa [dInt, hquadratic (n + 1)] using hn1
end MathlibExt.AlgebraicGeometry.EllipticCurve



-- created on 2026-10-20
-- updated on 2026-10-26
