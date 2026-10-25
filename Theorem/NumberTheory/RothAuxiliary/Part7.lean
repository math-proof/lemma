/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic
import Structure.NumberTheory.RothAuxiliary.Part3
set_option maxHeartbeats 999999

open scoped BigOperators

/-!
This file contains the auxiliary-polynomial machinery shared by Roth's theorem and Ridout's
S-adic extension. The public theorem abstracts their integrality difference as finite divisibility
data; the ordinary archimedean theorem is the specialization with no divisibility places.
-/


namespace MathlibExt.NumberTheory.RothAuxiliary

open scoped BigOperators nonZeroDivisors Polynomial

attribute [local instance] Matrix.seminormedAddCommGroup

theorem roth_ridout_finite_approximations_small_exponent
    (α : ℝ) (hα : IsAlgebraic ℚ α) (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    {ι : Type*} (S : Finset ι) (p : ι → ℕ) (μ ν : ι → ℝ)
    (hμ : ∀ l ∈ S, 0 ≤ μ l) (hν : ∀ l ∈ S, 0 ≤ ν l)
    (hσ : ∑ l ∈ S, (μ l + ν l) < 2 + ε) :
    Set.Finite {q : ℚ |
      |α - (q : ℝ)| <
          1 / Real.rpow (q.den : ℝ) (2 + ε - ∑ l ∈ S, (μ l + ν l)) ∧
        ∃ a b : ι → ℕ,
          ((∏ l ∈ S, p l ^ a l : ℕ) : ℤ) ∣ q.num ∧
          (∏ l ∈ S, p l ^ b l) ∣ q.den ∧
          ∀ l ∈ S,
            Real.rpow (q.den : ℝ) (μ l) ≤ (p l : ℝ) ^ a l ∧
            Real.rpow (q.den : ℝ) (ν l) ≤ (p l : ℝ) ^ b l} := by
  classical
  let σ := ∑ l ∈ S, (μ l + ν l)
  let A : Set ℚ := {q : ℚ |
    |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) (2 + ε - σ) ∧
      ∃ a b : ι → ℕ,
        ((∏ l ∈ S, p l ^ a l : ℕ) : ℤ) ∣ q.num ∧
        (∏ l ∈ S, p l ^ b l) ∣ q.den ∧
        ∀ l ∈ S,
          Real.rpow (q.den : ℝ) (μ l) ≤ (p l : ℝ) ^ a l ∧
          Real.rpow (q.den : ℝ) (ν l) ≤ (p l : ℝ) ^ b l}
  change A.Finite
  by_contra hinf
  let γ := ε / 16
  let θ := ε / 16
  let η := ε / 16
  let aR := 2 + ε
  let a := aR - σ
  let D := (rothIntegralPolynomial α).natDegree
  let n := ⌈(((D + 2 : ℕ) : ℝ) / (2 * γ ^ 2))⌉₊
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγhalf : γ < 1 / 2 := by dsimp [γ]; linarith
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθone : θ ≤ 1 := by dsimp [θ]; linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hD : 0 < D := rothIntegralPolynomial_natDegree_pos hα
  have hdenom : 0 < 2 * γ ^ 2 := by positivity
  have hnceil : (((D + 2 : ℕ) : ℝ) / (2 * γ ^ 2)) ≤ n := Nat.le_ceil _
  have hnR : 0 < (n : ℝ) :=
    (div_pos (by positivity) hdenom).trans_le hnceil
  have hn : 0 < n := by exact_mod_cast hnR
  have hparamHalf : (((D + 2 : ℕ) : ℝ)) ≤ 2 * (n + 1 : ℕ) * γ ^ 2 := by
    have hbase : (((D + 2 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) * γ ^ 2 := by
      calc
        (((D + 2 : ℕ) : ℝ)) =
            (2 * γ ^ 2) * (((D + 2 : ℕ) : ℝ) / (2 * γ ^ 2)) := by
              field_simp
        _ ≤ (2 * γ ^ 2) * n := mul_le_mul_of_nonneg_left hnceil hdenom.le
        _ = 2 * (n : ℝ) * γ ^ 2 := by ring
    calc
      (((D + 2 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) * γ ^ 2 := hbase
      _ ≤ 2 * (n + 1 : ℕ) * γ ^ 2 := by
        push_cast
        nlinarith [sq_nonneg γ]
  have hparamStrict : (((D + 2 : ℕ) : ℝ)) < 4 * (n + 1 : ℕ) * γ ^ 2 := by
    have hpos : 0 < 2 * (n + 1 : ℕ) * γ ^ 2 := by positivity
    nlinarith
  obtain ⟨δ, Q, R, hδ, hδone, hQtwo, hRone, hRoth⟩ :=
    roth_lemma n θ hθ hθone
  let β := min δ (1 / (2 * (n + 1 : ℕ)))
  have hβ : 0 < β := lt_min hδ (by positivity)
  have hβδ : β ≤ δ := min_le_left _ _
  have hβn : (n : ℝ) * β ≤ 1 := by
    have hβfrac : β ≤ 1 / (2 * (n + 1 : ℕ)) := min_le_right _ _
    calc
      (n : ℝ) * β ≤ (n : ℝ) * (1 / (2 * (n + 1 : ℕ))) :=
        mul_le_mul_of_nonneg_left hβfrac (Nat.cast_nonneg _)
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        push_cast
        nlinarith
  let K := ⌈2 / β⌉₊
  have hK : 2 ≤ β * K := by
    have hc : 2 / β ≤ (K : ℝ) := Nat.le_ceil _
    calc
      (2 : ℝ) = β * (2 / β) := by field_simp
      _ ≤ β * K := mul_le_mul_of_nonneg_left hc hβ.le
  have hKpos : 0 < K := by
    by_contra hnot
    have hz : K = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hz, Nat.cast_zero, mul_zero] at hK
    norm_num at hK
  let T := (n + 1 : ℕ) * (1 / 2 - γ)
  let g := aR * (T - θ) - (n + 1 : ℕ) * (1 + η)
  have hgform : g = ε / 16 * ((5 - ε) * (n + 1 : ℕ) - (2 + ε)) := by
    dsimp [g, aR, T, θ, η, γ]
    push_cast
    ring
  have hg : 0 < g := by
    rw [hgform]
    have hfive : 0 ≤ 5 - ε := by linarith
    have hmul : 5 - ε ≤ (5 - ε) * (n + 1 : ℕ) := by
      have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (Nat.le_add_left 1 n)
      nlinarith
    have hbracket : 0 < (5 - ε) * (n + 1 : ℕ) - (2 + ε) := by
      nlinarith
    positivity
  let H : ℕ := 8 * rothCoordinateBase α
  let C : ℝ := 8 * H * max 1 |α|
  have hH : 1 ≤ H := by
    dsimp [H]
    have := rothCoordinateBase_pos α
    omega
  have hC : 1 ≤ C := by
    dsimp [C]
    have hmax : (1 : ℝ) ≤ max 1 |α| := le_max_left _ _
    have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
    nlinarith
  obtain ⟨QH, hQH⟩ := roth_exists_rpow_threshold_of ((H : ℝ) ^ 2) hδ
  obtain ⟨QC, hQC⟩ := roth_exists_rpow_threshold_of (C ^ 2) (by positivity : 0 < g / 2)
  let N := max Q (max 2 (max QH QC))
  have hQN : Q ≤ N := le_max_left _ _
  have htwoN : 2 ≤ N :=
    (le_max_left 2 (max QH QC)).trans (le_max_right Q (max 2 (max QH QC)))
  have hQHN : QH ≤ N :=
    (le_max_left QH QC).trans (le_max_right 2 (max QH QC)) |>.trans
      (le_max_right Q (max 2 (max QH QC)))
  have hQCN : QC ≤ N :=
    (le_max_right QH QC).trans (le_max_right 2 (max QH QC)) |>.trans
      (le_max_right Q (max 2 (max QH QC)))
  have ha : 0 < a := by
    dsimp [a, aR, σ]
    linarith
  have hAsub : A ⊆ {q : ℚ |
      |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) a} := by
    intro q hq
    simpa [A, a] using hq.1
  obtain ⟨q, hqA, hq0N, hchain⟩ :=
    roth_ridout_exists_approximation_chain (α := α) (p := a) ha A hAsub hinf
      n N K
  have happrox : ∀ h,
      |α - (q h : ℝ)| < 1 / Real.rpow ((q h).den : ℝ) a :=
    fun h ↦ hAsub (hqA h)
  have hwit : ∀ h, ∃ av bv : ι → ℕ,
      ((∏ l ∈ S, p l ^ av l : ℕ) : ℤ) ∣ (q h).num ∧
      (∏ l ∈ S, p l ^ bv l) ∣ (q h).den ∧
      ∀ l ∈ S,
        Real.rpow ((q h).den : ℝ) (μ l) ≤ (p l : ℝ) ^ av l ∧
        Real.rpow ((q h).den : ℝ) (ν l) ≤ (p l : ℝ) ^ bv l := by
    intro h
    exact (hqA h).2
  choose av bv hav using hwit
  let d : Fin (n + 1) → ℕ := fun h ↦ (q h).den
  have hKone : 1 ≤ K := hKpos
  have hdstep : ∀ i : Fin n, d i.castSucc ≤ d i.succ := by
    intro i
    calc
      d i.castSucc = d i.castSucc ^ 1 := (pow_one _).symm
      _ ≤ d i.castSucc ^ K :=
        pow_le_pow_right₀ (q i.castSucc).pos hKone
      _ ≤ d i.succ := (hchain i).le
  have hdmono : Monotone d := Fin.monotone_iff_le_succ.mpr hdstep
  have hd0two : 2 ≤ d 0 := htwoN.trans hq0N.le
  have hd : ∀ h, 2 ≤ d h := fun h ↦ hd0two.trans (hdmono (Fin.zero_le h))
  obtain ⟨r, hrlarge, hranti, hsep, hpower, hsum, hupper⟩ :=
    roth_exists_balanced_degrees d K R δ β η hd hdmono hchain
      hβ hβδ hη hβn hK
  have hrpos : ∀ h, 0 < r h := fun h ↦
    lt_of_lt_of_le Nat.zero_lt_one (hRone.trans (hrlarge h))
  obtain ⟨c, hc, hcvan, hcbalanced, hcl1⟩ :=
    roth_ridout_exists_auxiliary_coeff α hα hrpos
      (by omega : 0 < n + 1) hγ hγhalf
      (by simpa [D] using hparamStrict) (by simpa [D] using hparamHalf)
  let P := rothMvOfCoeff c
  have hPne : P ≠ 0 := rothMvOfCoeff_ne_zero hc
  have hPdegree : rothDegreeBound P r := rothMvOfCoeff_degreeBound c
  have hPvan : rothMvVanishesBelow
      (MvPolynomial.map (algebraMap ℤ ℝ) P) (fun _h ↦ α) r T := by
    exact rothVanishesBelow_to_mv hcvan
  have hheight : (rothMvL1 P : ℝ) ≤
      Real.rpow (q 0).den (δ * r 0) := by
    have hbase : (H : ℝ) ^ 2 ≤ Real.rpow (q 0).den δ :=
      hQH _ (hQHN.trans hq0N.le)
    calc
      (rothMvL1 P : ℝ) ≤ ((H ^ (∑ h, r h) : ℕ) : ℝ) := by
        exact_mod_cast hcl1
      _ = (H : ℝ) ^ (∑ h, r h) := by norm_cast
      _ ≤ Real.rpow (q 0).den (δ * r 0) :=
        roth_pow_le_rpow_of_le_twice H (q 0).den δ (∑ h, r h) (r 0)
          (by exact_mod_cast hH) (by positivity) hsum hbase
  let Q₀ : ℝ := ((q 0).den : ℝ) ^ r 0
  have hQ₀ : 1 < Q₀ := by
    dsimp [Q₀]
    apply one_lt_pow₀
    · exact_mod_cast hd0two
    · exact (hrpos 0).ne'
  have hpowerR : ∀ h, Q₀ ≤ ((q h).den : ℝ) ^ r h := by
    intro h
    dsimp [Q₀]
    exact_mod_cast hpower h
  have herr : ∀ l : RothMvIndex (n + 1),
      ∏ h, |(q h : ℝ) - α| ^ l h ≤
        Real.rpow Q₀ (-a * rothMvWeight r l) := by
    exact roth_product_approximation_bound_of_den_power (fun _h ↦ α) q r hrpos
      a Q₀ ha.le (zero_lt_one.trans hQ₀) hpowerR happrox
  have hdenUpper : (rothDenProduct q r : ℝ) ≤
      Real.rpow Q₀ ((n + 1 : ℕ) * (1 + η)) := by
    apply roth_denProduct_le_rpow q r Q₀ η (zero_le_one.trans hQ₀.le)
    intro h
    simpa [Q₀, d] using hupper h
  let F : ℝ :=
    (((8 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
      ∏ _h : Fin (n + 1), max 1 |α| ^ r _h)
  have hFnonneg : 0 ≤ F := by dsimp [F]; positivity
  have hF : F ≤ Real.rpow Q₀ (g / 2) := by
    have hCbase : C ^ 2 ≤ Real.rpow (q 0).den (g / 2) :=
      hQC _ (hQCN.trans hq0N.le)
    have hCpow : C ^ (∑ h, r h) ≤
        Real.rpow (q 0).den ((g / 2) * r 0) :=
      roth_pow_le_rpow_of_le_twice C (q 0).den (g / 2) (∑ h, r h) (r 0)
        hC (by positivity) hsum hCbase
    have hraw : F ≤ C ^ (∑ h, r h) := by
      dsimp [F, C]
      rw [Finset.prod_pow_eq_pow_sum]
      have hcl1R : (rothMvL1 P : ℝ) ≤ (H : ℝ) ^ (∑ h, r h) := by
        exact_mod_cast hcl1
      calc
        ((8 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
              max 1 |α| ^ (∑ h, r h) ≤
            ((8 : ℝ) ^ (∑ h, r h) * (H : ℝ) ^ (∑ h, r h)) *
              max 1 |α| ^ (∑ h, r h) := by
                push_cast
                gcongr
        _ = (8 * (H : ℝ) * max 1 |α|) ^ (∑ h, r h) := by
          rw [mul_pow, mul_pow]
    refine hraw.trans (hCpow.trans_eq ?_)
    dsimp [Q₀]
    calc
      Real.rpow (q 0).den ((g / 2) * r 0) =
          Real.rpow (q 0).den ((r 0 : ℝ) * (g / 2)) := by congr 1; ring
      _ = Real.rpow (Real.rpow (q 0).den (r 0 : ℝ)) (g / 2) :=
        Real.rpow_mul (by positivity) _ _
      _ = Real.rpow (((q 0).den : ℝ) ^ r 0) (g / 2) := by
        congr 1
        exact Real.rpow_natCast _ _
  have hmaster : (rothDenProduct q r : ℝ) * F <
      Real.rpow Q₀ (aR * (T - θ)) := by
    apply roth_mul_lt_rpow Q₀ (rothDenProduct q r) F
      ((n + 1 : ℕ) * (1 + η)) (g / 2) (aR * (T - θ)) hQ₀
      hFnonneg hdenUpper hF
    dsimp [g]
    nlinarith
  let s := σ * (T - θ)
  have hdiv : ∀ i : RothMvIndex (n + 1), rothMvWeight r i ≤ θ →
      ∃ G : ℕ, Real.rpow Q₀ s ≤ G ∧
        (G : ℤ) ∣ rothClearEval (rothMvHasse i P) q r := by
    intro i hi
    simpa [P, s, σ] using
      roth_ridout_exists_hasse_clear_divisor S p q r av bv μ ν c Q₀ T θ i
        hrpos hQ₀ hθ.le hμ hν hpowerR
        (fun h ↦ (hav h).1) (fun h ↦ (hav h).2.1)
        (fun h l hl ↦ (hav h).2.2 l hl |>.1)
        (fun h l hl ↦ (hav h).2.2 l hl |>.2)
        hcbalanced hi
  have hmaster' : (rothDenProduct q r : ℝ) *
        (((8 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
          ∏ h, max 1 |(fun _h : Fin (n + 1) ↦ α) h| ^ r h) <
      Real.rpow Q₀ (s + a * (T - θ)) := by
    rw [show s + a * (T - θ) = aR * (T - θ) by
      dsimp [s, a]
      ring]
    simpa [F] using hmaster
  have hzero := roth_ridout_hasse_eq_zero_at_rational_of_taylor_bound P
    (fun _h ↦ α) q r hrpos hPdegree T a Q₀ θ s hPvan
    ha.le hQ₀ herr hdiv hmaster'
  have hratvan := roth_rational_vanishing_of_real_hasse_zero P q r θ hzero
  let X : RothLemmaInput n δ Q R := {
    P := P
    r := r
    q := q
    P_ne := hPne
    P_degree := hPdegree
    r_large := hrlarge
    den_large := hQN.trans hq0N.le
    den_monotone := by simpa [d] using hdmono
    r_antitone := hranti
    separated := hsep
    den_power := by simpa [d] using hpower
    height := hheight
  }
  exact hRoth X hratvan

/-- Roth's finiteness theorem with an abstract finite collection of divisibility places.

The functions `p`, `μ`, and `ν` encode lower bounds on powers dividing the numerator and
denominator. Taking `S` empty gives the usual archimedean approximation set. -/
theorem finite_of_divisible_approximations
    (α : ℝ) (hα : IsAlgebraic ℚ α)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    {ι : Type*} (S : Finset ι) (p : ι → ℕ) (μ ν : ι → ℝ)
    (hμ : ∀ l ∈ S, 0 ≤ μ l) (hν : ∀ l ∈ S, 0 ≤ ν l)
    (hσ : ∑ l ∈ S, (μ l + ν l) < 2 + ε) :
    Set.Finite {q : ℚ |
      |α - (q : ℝ)| <
          1 / Real.rpow (q.den : ℝ) (2 + ε - ∑ l ∈ S, (μ l + ν l)) ∧
        ∃ a b : ι → ℕ,
          ((∏ l ∈ S, p l ^ a l : ℕ) : ℤ) ∣ q.num ∧
          (∏ l ∈ S, p l ^ b l) ∣ q.den ∧
          ∀ l ∈ S,
            Real.rpow (q.den : ℝ) (μ l) ≤ (p l : ℝ) ^ a l ∧
            Real.rpow (q.den : ℝ) (ν l) ≤ (p l : ℝ) ^ b l} :=
  roth_ridout_finite_approximations_small_exponent α hα ε hε hεone
    S p μ ν hμ hν hσ

end MathlibExt.NumberTheory.RothAuxiliary
