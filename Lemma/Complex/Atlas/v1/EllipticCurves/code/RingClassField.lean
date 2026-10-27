import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.EllipticCurves.code.RingClassField.Part3
open NumberField Elliptic_Curves ImagQuadPrimeSplitting CMMethod CMMethod.TwistSelection
open Polynomial
open Elliptic_Curves
open Elliptic_Curves ProperIdealInvertible
open Elliptic_Curves ImagQuadPrimeSplitting


namespace Elliptic_Curves

/--
[normEquation_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean)
-/
@[path]
lemma normEquation_iff
  {D : ℤ}
  {p : ℕ}
  {t v : ℤ} :
-- imply
  NormEquation D p t v ↔ 4 * (p : ℤ) = t ^ 2 - v ^ 2 * D :=
-- proof
  Iff.rfl

end Elliptic_Curves

namespace Elliptic_Curves

/--
[normEquation_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean)
-/
@[path]
lemma normEquation_neg
  {D : ℤ}
  {p : ℕ}
  {t v : ℤ} :
-- imply
  NormEquation D p t v ↔ NormEquation D p (-t) (-v) := by
-- proof
  simp only [NormEquation, neg_sq]

end Elliptic_Curves

namespace Elliptic_Curves

/--
[normEquation_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean)
-/
@[path]
lemma normEquation_sq_le
  {D : ℤ}
  {p : ℕ}
  {t v : ℤ}
-- given
  (hD : D < 0)
  (hne : NormEquation D p t v) :
-- imply
  t ^ 2 ≤ 4 * (p : ℤ) := by
-- proof
  unfold NormEquation at hne
  nlinarith [sq_nonneg v]

end Elliptic_Curves

namespace Elliptic_Curves

/--
[kroneckerSymbol_values](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean)
-/
@[path]
lemma kroneckerSymbol_values
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {D : ℤ} :
-- imply
  kroneckerSymbol p D = -1 ∨ kroneckerSymbol p D = 0 ∨ kroneckerSymbol p D = 1 := by
-- proof
  unfold kroneckerSymbol
  split_ifs
  · right; left; rfl
  · right; right; rfl
  · left; rfl
  · have hq := quadraticChar_isQuadratic (ZMod p) (D : ZMod p)
    simp only [legendreSym]
    obtain h | h | h := hq
    · right; left; exact_mod_cast h
    · right; right; exact_mod_cast h
    · left; exact_mod_cast h

end Elliptic_Curves

namespace Elliptic_Curves

/--
[kroneckerSymbol_odd_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean)
-/
@[path]
lemma kroneckerSymbol_odd_prime
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {D : ℤ}
-- given
  (hodd : p ≠ 2) :
-- imply
  kroneckerSymbol p D = legendreSym p D := by
-- proof
  simp [kroneckerSymbol, hodd]
namespace Deuring
open Polynomial

end Elliptic_Curves

namespace ImagQuadPrimeSplitting

/--
[card_filter_sq_add_eq_zero_ZMod2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean)
-/
@[path]
lemma card_filter_sq_add_eq_zero_ZMod2
  {c : ZMod 2} :
-- imply
  (Finset.univ.filter (fun x : ZMod 2 => x ^ 2 + c = 0)).card = 1 := by
-- proof
  revert c; decide

end ImagQuadPrimeSplitting

namespace ImagQuadPrimeSplitting

/--
[card_filter_sq_sub_x_add_ZMod2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean)
-/
@[path]
lemma card_filter_sq_sub_x_add_ZMod2
  {c : ZMod 2} :
-- imply
  (Finset.univ.filter (fun x : ZMod 2 => x ^ 2 - x + c = 0)).card = if c = 0 then 2 else 0 := by
-- proof
  revert c; decide

end ImagQuadPrimeSplitting

namespace ImagQuadPrimeSplitting

/--
[numIdealsOfNorm_eq_one_add_kroneckerSymbol](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean)
-/
@[path]
lemma numIdealsOfNorm_eq_one_add_kroneckerSymbol
  {D : ℤ}
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
-- given
  (hD : IsImagQuadDiscriminant D) :
-- imply
  numIdealsOfNorm D p = 1 + kroneckerSymbol p D := by
-- proof
  obtain ⟨hDneg, hDmod⟩ := hD
  by_cases hp2 : p = 2
  ·
    subst hp2
    unfold numIdealsOfNorm rootsMinPolyMod kroneckerSymbol
    obtain hD0 | hD1 := hDmod
    ·
      have hDeven : D % 2 = 0 := by omega
      have hD_not1 : ¬(D % 4 = 1) := by omega
      simp only [hD_not1, ite_false, hDeven, ite_true]
      rw [card_filter_sq_add_eq_zero_ZMod2]; norm_cast
    ·
      have hDodd : ¬(D % 2 = 0) := by omega
      simp only [hD1, ite_true, hDodd, ite_false]
      have hDmod8 : D % 8 = 1 ∨ D % 8 = 5 := by omega
      obtain h8_1 | h8_5 := hDmod8
      · have hc0 : ((((1 - D) / 4 : ℤ) : ZMod 2) = 0) := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Int.dvd_of_emod_eq_zero (by omega)
        rw [card_filter_sq_sub_x_add_ZMod2, if_pos hc0]
        have : D % 8 = 1 ∨ D % 8 = 7 := Or.inl h8_1
        simp [this]
      · have hc1 : ((((1 - D) / 4 : ℤ) : ZMod 2) ≠ 0) := by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; intro ⟨k, hk⟩; omega
        rw [card_filter_sq_sub_x_add_ZMod2, if_neg hc1]
        have : ¬(D % 8 = 1 ∨ D % 8 = 7) := by omega
        simp [this]
  ·
    have hodd : p ≠ 2 := hp2
    rw [kroneckerSymbol_odd_prime hodd]
    have hprime : Nat.Prime p := hp.out
    have hcard_sqrts := legendreSym.card_sqrts p hodd D
    suffices h : (rootsMinPolyMod D p).card = {x : ZMod p | x ^ 2 = (D : ZMod p)}.toFinset.card by
      rw [numIdealsOfNorm, h]; linarith
    have h2inv : IsUnit (2 : ZMod p) :=
      ZMod.isUnit_prime_of_not_dvd Nat.prime_two
        (fun h => hodd (hprime.eq_one_or_self_of_dvd 2 h |>.resolve_left (by omega) |>.symm))
    have h2ne : (2 : ZMod p) ≠ 0 := IsUnit.ne_zero h2inv
    have h4_ne : (4 : ZMod p) ≠ 0 := by
      have : IsUnit (4 : ZMod p) := by
        rw [show (4 : ZMod p) = 2 * 2 from by norm_num]; exact h2inv.mul h2inv
      exact IsUnit.ne_zero this
    obtain ⟨u, hu⟩ := h2inv
    have h2u_inv : (2 : ZMod p) * ↑u⁻¹ = 1 := by
      rw [← hu]; exact_mod_cast u.mul_inv
    obtain hD0 | hD1 := hDmod
    ·
      simp only [rootsMinPolyMod, show ¬(D % 4 = 1) from by omega, ite_false]
      have h4_cast : (4 : ZMod p) * ((-D / 4 : ℤ) : ZMod p) = ((-D : ℤ) : ZMod p) := by
        rw [← Int.cast_ofNat, ← Int.cast_mul]; congr 1; omega
      have h_fwd : ∀ x : ZMod p, x ^ 2 + ((-D / 4 : ℤ) : ZMod p) = 0 →
        (2 * x) ^ 2 = (D : ZMod p) := by
        intro x hx
        have : (2 * x) ^ 2 = 4 * (x ^ 2 + ((-D / 4 : ℤ) : ZMod p)) + (D : ZMod p) := by
          rw [show (2 * x) ^ 2 = 4 * x ^ 2 from by ring, mul_add, h4_cast]; push_cast; ring
        rw [hx, mul_zero, zero_add] at this; exact this
      have h_bwd : ∀ y : ZMod p, y ^ 2 = (D : ZMod p) →
        (↑u⁻¹ * y) ^ 2 + ((-D / 4 : ℤ) : ZMod p) = 0 := by
        intro y hy
        have : (4 : ZMod p) * ((↑u⁻¹ * y) ^ 2 + ((-D / 4 : ℤ) : ZMod p)) = 0 := by
          have h4u : (4 : ZMod p) * (↑u⁻¹ * y) ^ 2 = y ^ 2 := by
            rw [show (4 : ZMod p) * (↑u⁻¹ * y) ^ 2 = (2 * ↑u⁻¹) ^ 2 * y ^ 2 from by ring]
            rw [h2u_inv, one_pow, one_mul]
          rw [mul_add, h4u, h4_cast, hy]; push_cast; ring
        exact (mul_eq_zero.mp this).resolve_left h4_ne
      apply Finset.card_bij (fun x _ => 2 * x)
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_fwd x hx
      · intro x₁ _ x₂ _ h; exact mul_left_cancel₀ h2ne h
      · intro y hy
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact ⟨↑u⁻¹ * y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_bwd y hy⟩,
          by rw [show (2 : ZMod p) * (↑u⁻¹ * y) = (2 * ↑u⁻¹) * y from by ring, h2u_inv, one_mul]⟩
    ·
      simp only [rootsMinPolyMod, show D % 4 = 1 from hD1, ite_true]
      have h4_cast : (4 : ZMod p) * (((1 - D) / 4 : ℤ) : ZMod p) = ((1 - D : ℤ) : ZMod p) := by
        rw [← Int.cast_ofNat, ← Int.cast_mul]; congr 1; omega
      have h_fwd : ∀ x : ZMod p, x ^ 2 - x + ((1 - D) / 4 : ℤ) = 0 →
        (2 * x - 1) ^ 2 = (D : ZMod p) := by
        intro x hx
        have : (2 * x - 1) ^ 2 = 4 * (x ^ 2 - x + ((1 - D) / 4 : ℤ)) + (D : ZMod p) := by
          rw [show (2 * x - 1) ^ 2 = 4 * x ^ 2 - 4 * x + 1 from by ring,
            show (4 : ZMod p) * (x ^ 2 - x + ((1 - D) / 4 : ℤ)) =
              4 * x ^ 2 - 4 * x + 4 * ((1 - D) / 4 : ℤ) from by ring,
            h4_cast]; push_cast; ring
        rw [hx, mul_zero, zero_add] at this; exact this
      have h_bwd : ∀ y : ZMod p, y ^ 2 = (D : ZMod p) →
        (↑u⁻¹ * (y + 1)) ^ 2 - (↑u⁻¹ * (y + 1)) + ((1 - D) / 4 : ℤ) = 0 := by
        intro y hy
        have key : 2 * (↑u⁻¹ * (y + 1)) - 1 = y := by
          rw [show (2 : ZMod p) * (↑u⁻¹ * (y + 1)) = (2 * ↑u⁻¹) * (y + 1) from by ring]
          rw [h2u_inv, one_mul, add_sub_cancel_right]
        have h1 : (2 * (↑u⁻¹ * (y + 1)) - 1) ^ 2 =
          4 * ((↑u⁻¹ * (y + 1)) ^ 2 - (↑u⁻¹ * (y + 1)) + ((1 - D) / 4 : ℤ)) + (D : ZMod p) := by
          rw [show (2 * (↑u⁻¹ * (y + 1)) - 1) ^ 2 =
            4 * (↑u⁻¹ * (y + 1)) ^ 2 - 4 * (↑u⁻¹ * (y + 1)) + 1 from by ring,
            show (4 : ZMod p) * ((↑u⁻¹ * (y + 1)) ^ 2 - (↑u⁻¹ * (y + 1)) + ((1 - D) / 4 : ℤ)) =
              4 * (↑u⁻¹ * (y + 1)) ^ 2 - 4 * (↑u⁻¹ * (y + 1)) + 4 * ((1 - D) / 4 : ℤ) from by ring,
            h4_cast]; push_cast; ring
        rw [key, hy] at h1
        have h2 : (4 : ZMod p) * ((↑u⁻¹ * (y + 1)) ^ 2 - (↑u⁻¹ * (y + 1)) + ((1 - D) / 4 : ℤ)) = 0 := by
          have : (D : ZMod p) - (D : ZMod p) =
            4 * ((↑u⁻¹ * (y + 1)) ^ 2 - (↑u⁻¹ * (y + 1)) + ((1 - D) / 4 : ℤ)) + (D : ZMod p) - (D : ZMod p) := by
            rw [← h1]
          simp only [sub_self, add_sub_cancel_right] at this
          exact this.symm
        exact (mul_eq_zero.mp h2).resolve_left h4_ne
      apply Finset.card_bij (fun x _ => 2 * x - 1)
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_fwd x hx
      · intro x₁ _ x₂ _ h
        have : 2 * x₁ = 2 * x₂ := by linear_combination h
        exact mul_left_cancel₀ h2ne this
      · intro y hy
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact ⟨↑u⁻¹ * (y + 1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_bwd y hy⟩,
          by rw [show (2 : ZMod p) * (↑u⁻¹ * (y + 1)) = (2 * ↑u⁻¹) * (y + 1) from by ring,
            h2u_inv, one_mul, add_sub_cancel_right]⟩
end ImagQuadPrimeSplitting
namespace ImagQuadPrimeFactorization
open Elliptic_Curves ProperIdealInvertible


namespace CMMethod.TwistSelection

/--
[exists_curve_or_twist_with_order](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean)
-/
@[path]
lemma exists_curve_or_twist_with_order
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {t : ℤ}
-- given
  (hfrob : Hasse.traceFrobenius E = t ∨ Hasse.traceFrobenius E = -t)
  (hE : Hasse.numPoints E ≤ 2 * Fintype.card F + 2) :
-- imply
  (Hasse.numPoints E : ℤ) = (Fintype.card F : ℤ) + 1 - t ∨ (QuadraticTwist.twistNumPoints E : ℤ) = (Fintype.card F : ℤ) + 1 - t := by
-- proof
  obtain h | h := hfrob
  ·
    left
    have := Hasse.numPoints_eq_card_sub_trace E
    linarith
  ·
    right
    have hadd := QuadraticTwist.numPoints_add_twist E hE
    have hnum := Hasse.numPoints_eq_card_sub_trace E
    omega

end CMMethod.TwistSelection


-- created on 2026-10-23
