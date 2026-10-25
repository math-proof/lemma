import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
/-!
# Frobenius theorem on real division algebras

Proves the classification of finite-dimensional associative division ℝ-algebras.
-/


namespace FrobeniusDivision

-- Helper 1: the structure map ℝ → A is injective (ℝ is a field, A nontrivial).
theorem algMap_injective {A : Type*} [DivisionRing A] [Algebra ℝ A] :
    Function.Injective (algebraMap ℝ A) :=
  RingHom.injective (algebraMap ℝ A)

-- Helper 2: every element is integral over ℝ (finite-dimensionality).
theorem isIntegral_mem {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] (x : A) : IsIntegral ℝ x := by
  have h : Algebra.IsIntegral ℝ A := Algebra.IsIntegral.of_finite ℝ A
  exact h.isIntegral x

-- Helper 3: every element satisfies a real polynomial of degree ≤ 2.
theorem minpoly_natDegree_le_two {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] (x : A) : (minpoly ℝ x).natDegree ≤ 2 := by
  have hirr : Irreducible (minpoly ℝ x) :=
    minpoly.irreducible (isIntegral_mem x)
  have hdeg : (minpoly ℝ x).degree ≤ 2 := Irreducible.degree_le_two hirr
  exact Polynomial.natDegree_le_of_degree_le hdeg

-- Helper 4 (degree analysis): a nonreal element has quadratic minpoly, giving
-- an explicit relation `x ^ 2 + c₁ • x + c₀ = 0`.
theorem quad_relation {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] {x : A} (hx : ∀ r : ℝ, algebraMap ℝ A r ≠ x) :
    ∃ c₁ c₀ : ℝ, x ^ 2 + algebraMap ℝ A c₁ * x + algebraMap ℝ A c₀ = 0 := by
  have hint : IsIntegral ℝ x := isIntegral_mem x
  have hmonic : (minpoly ℝ x).Monic := minpoly.monic hint
  have hdeg2 : (minpoly ℝ x).natDegree ≤ 2 := minpoly_natDegree_le_two x
  have haeval : Polynomial.aeval x (minpoly ℝ x) = 0 := minpoly.aeval ℝ x
  have hdeg0 : (minpoly ℝ x).natDegree ≠ 0 := by
    intro h0
    have hform : minpoly ℝ x = Polynomial.C ((minpoly ℝ x).coeff 0) := by
      ext n
      simp only [Polynomial.coeff_C]
      by_cases hn : n = 0
      · subst hn; rfl
      · rw [ite_eq_right hn]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hc1 : (minpoly ℝ x).coeff 0 = 1 := by
      have hmc := hmonic.coeff_natDegree
      rw [h0] at hmc
      exact hmc
    rw [hform, Polynomial.aeval_C] at haeval
    have hcz : (minpoly ℝ x).coeff 0 = 0 :=
      algMap_injective (by rw [haeval, map_zero])
    rw [hc1] at hcz
    exact one_ne_zero hcz
  have hdeg1 : (minpoly ℝ x).natDegree ≠ 1 := by
    intro h1
    have hform : minpoly ℝ x
        = Polynomial.X + Polynomial.C ((minpoly ℝ x).coeff 0) := by
      ext n
      rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
      by_cases hn0 : n = 0
      · subst hn0
        simp
      · by_cases hn1 : n = 1
        · subst hn1
          have hmc := hmonic.coeff_natDegree
          rw [h1] at hmc
          simp [hmc]
        · have h0 : (minpoly ℝ x).coeff n = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          have e1 : (1 : ℕ) ≠ n := fun h => hn1 h.symm
          simp [h0, hn0, e1]
    rw [hform] at haeval
    simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C] at haeval
    have h2 : x = -(algebraMap ℝ A ((minpoly ℝ x).coeff 0)) :=
      eq_neg_of_add_eq_zero_left haeval
    have hxmem : x = algebraMap ℝ A (-((minpoly ℝ x).coeff 0)) := by
      rw [map_neg]
      exact h2
    exact hx _ hxmem.symm
  have hdeg : (minpoly ℝ x).natDegree = 2 := by omega
  have hform : minpoly ℝ x = Polynomial.X ^ 2
      + Polynomial.C ((minpoly ℝ x).coeff 1) * Polynomial.X
      + Polynomial.C ((minpoly ℝ x).coeff 0) := by
    ext n
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
    by_cases hn0 : n = 0
    · subst hn0
      simp
    · by_cases hn1 : n = 1
      · subst hn1
        have hmc := hmonic.coeff_natDegree
        rw [hdeg] at hmc
        simp
      · by_cases hn2 : n = 2
        · subst hn2
          have hmc := hmonic.coeff_natDegree
          rw [hdeg] at hmc
          simp [hmc]
        · have h0 : (minpoly ℝ x).coeff n = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          have e1 : (1 : ℕ) ≠ n := fun h => hn1 h.symm
          simp [h0, hn0, e1, hn2]
  rw [hform] at haeval
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C] at haeval
  exact ⟨_, _, haeval⟩

-- Helper 5 (complete the square): a nonreal element yields `u` with `u * u = -1`.
theorem exists_sq_eq_neg_one {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] {x : A} (hx : ∀ r : ℝ, algebraMap ℝ A r ≠ x) :
    ∃ u : A, u * u = -1 := by
  obtain ⟨c₁, c₀, hquad⟩ := quad_relation hx
  have hcentral : ∀ y : ℝ, algebraMap ℝ A y * x = x * algebraMap ℝ A y :=
    fun y => (Algebra.commute_algebraMap_left y x).eq
  have hxx : x ^ 2
      = -(algebraMap ℝ A c₁ * x) - algebraMap ℝ A c₀ := by
    have h2 : x ^ 2 + (algebraMap ℝ A c₁ * x + algebraMap ℝ A c₀) = 0 := by
      rw [← add_assoc]
      exact hquad
    have h3 := eq_neg_of_add_eq_zero_left h2
    rw [neg_add] at h3
    rw [sub_eq_add_neg]
    exact h3
  have hm1 : algebraMap ℝ A c₁ * x
      = algebraMap ℝ A (c₁ / 2) * x + algebraMap ℝ A (c₁ / 2) * x := by
    have hc : algebraMap ℝ A c₁
        = algebraMap ℝ A (c₁ / 2) + algebraMap ℝ A (c₁ / 2) := by
      have hc2 : c₁ = c₁ / 2 + c₁ / 2 := by ring
      conv_lhs => rw [hc2]
      rw [map_add]
    rw [hc, add_mul]
  have hmm : algebraMap ℝ A (c₁ / 2) * algebraMap ℝ A (c₁ / 2)
      = algebraMap ℝ A ((c₁ / 2) ^ 2) := by
    rw [← map_mul, pow_two]
  set t : A := x + algebraMap ℝ A (c₁ / 2) with ht
  have hexpand : t * t = x ^ 2
      + (algebraMap ℝ A (c₁ / 2) * x + algebraMap ℝ A (c₁ / 2) * x)
      + algebraMap ℝ A (c₁ / 2) * algebraMap ℝ A (c₁ / 2) := by
    have e1 : (x + algebraMap ℝ A (c₁ / 2)) * (x + algebraMap ℝ A (c₁ / 2))
        = x * x + x * algebraMap ℝ A (c₁ / 2)
          + (algebraMap ℝ A (c₁ / 2) * x
            + algebraMap ℝ A (c₁ / 2) * algebraMap ℝ A (c₁ / 2)) := by
      rw [add_mul, mul_add, mul_add]
    have e2 : x * algebraMap ℝ A (c₁ / 2)
        = algebraMap ℝ A (c₁ / 2) * x := (hcentral (c₁ / 2)).symm
    rw [ht, e1, e2, ← pow_two]
    abel
  have htsq : t * t = algebraMap ℝ A ((c₁ / 2) ^ 2 - c₀) := by
    rw [hexpand, hxx, hm1, hmm, map_sub]
    abel
  by_cases hge : 0 ≤ (c₁ / 2) ^ 2 - c₀
  · -- Nonnegative case: `t` is (plus/minus) a real, contradicting `hx`.
    set s := Real.sqrt ((c₁ / 2) ^ 2 - c₀) with hs
    have hss : s * s = (c₁ / 2) ^ 2 - c₀ := Real.mul_self_sqrt hge
    have hts : t * t
        = algebraMap ℝ A s * algebraMap ℝ A s := by
      rw [htsq, ← hss, ← map_mul]
    have hfac : (t - algebraMap ℝ A s) * (t + algebraMap ℝ A s) = 0 := by
      have hcen : algebraMap ℝ A s * t = t * algebraMap ℝ A s :=
        (Algebra.commute_algebraMap_left s t).eq
      have hexp : (t - algebraMap ℝ A s) * (t + algebraMap ℝ A s)
          = (t * t + t * algebraMap ℝ A s)
            - (algebraMap ℝ A s * t
              + algebraMap ℝ A s * algebraMap ℝ A s) := by
        noncomm_ring
      rw [hexp, hcen, hts]
      abel
    obtain h | h := mul_eq_zero.mp hfac
    · have htS : t = algebraMap ℝ A s := sub_eq_zero.mp h
      have hsub : x = t - algebraMap ℝ A (c₁ / 2) := by
        rw [ht]
        abel
      have hxeq : x = algebraMap ℝ A (s - c₁ / 2) := by
        rw [hsub, htS, ← map_sub]
      exact (hx _ hxeq.symm).elim
    · have htS : t = -(algebraMap ℝ A s) := eq_neg_of_add_eq_zero_left h
      have hsub : x = t - algebraMap ℝ A (c₁ / 2) := by
        rw [ht]
        abel
      have hxeq : x = algebraMap ℝ A (-s - c₁ / 2) := by
        rw [hsub, htS, map_sub, map_neg]
      exact (hx _ hxeq.symm).elim
  · -- Negative case: normalize `t` to a square root of `-1`.
    push Not at hge
    have hpos : 0 < -((c₁ / 2) ^ 2 - c₀) := neg_pos.mpr hge
    set d := Real.sqrt (-((c₁ / 2) ^ 2 - c₀)) with hd
    have hdd : d * d = -((c₁ / 2) ^ 2 - c₀) :=
      Real.mul_self_sqrt (le_of_lt hpos)
    have hd0 : d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    have hSd0 : algebraMap ℝ A d ≠ 0 := by
      intro hz
      have hz' : algebraMap ℝ A d = algebraMap ℝ A 0 := by
        rw [hz, map_zero]
      exact hd0 (algMap_injective hz')
    have hcommd : algebraMap ℝ A d * t = t * algebraMap ℝ A d :=
      (Algebra.commute_algebraMap_left d t).eq
    have hinvcomm : (algebraMap ℝ A d)⁻¹ * t
        = t * (algebraMap ℝ A d)⁻¹ := by
      apply mul_left_cancel₀ hSd0
      rw [← mul_assoc (algebraMap ℝ A d) _ _,
        mul_inv_cancel₀ hSd0, one_mul,
        ← mul_assoc (algebraMap ℝ A d) t _,
        hcommd, mul_assoc t _ _,
        mul_inv_cancel₀ hSd0, mul_one]
    refine ⟨t * (algebraMap ℝ A d)⁻¹, ?_⟩
    set w : A := (algebraMap ℝ A d)⁻¹ with hw
    have hmove : t * w * (t * w) = (t * t) * (w * w) := by
      rw [mul_assoc t w (t * w), ← mul_assoc w t w, hinvcomm,
        mul_assoc t w w, ← mul_assoc t t (w * w)]
    have hww : w * w = algebraMap ℝ A ((d * d)⁻¹) := by
      rw [hw, ← mul_inv_rev, ← map_mul, ← map_inv₀]
    have hed : ((c₁ / 2) ^ 2 - c₀) * ((d * d)⁻¹) = -1 := by
      have hene : (c₁ / 2) ^ 2 - c₀ ≠ 0 := ne_of_lt hge
      rw [hdd, inv_neg, mul_neg, mul_inv_cancel₀ hene]
    rw [hmove, htsq, hww, ← map_mul, hed, map_neg, map_one]

end FrobeniusDivision
