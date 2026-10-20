/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Upper.lean -/

import sympy.atlas.NumberTheory.PrimeInterval.Breusch.Grid
import sympy.atlas.NumberTheory.PrimeInterval.Breusch.Lower
import sympy.atlas.NumberTheory.PrimeInterval.Breusch.Theta
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.Computability.Reduce
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Breusch upper bound via the continuous `G`-function

The continuous `G9r` function, its identification with the grid `G9`, the `p`-adic
valuation identity for the weighted product, and the resulting upper bound
`logF9_upper` under the assumption that `(1890 * n, 2100 * n]` holds no prime.
-/

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

open Nat Finset

/-- Continuous `G`-function: Möbius-weighted floors at real `x`. -/
noncomputable def G9r (x : ℝ) : ℤ := w9.toFinset.sum (fun q : ℕ × ℤ =>
  q.2 * ((Int.ofNat ⌊((10*Q9:ℕ):ℝ)*x/(q.1:ℝ)⌋₊)
    - (Int.ofNat ⌊((9*Q9:ℕ):ℝ)*x/(q.1:ℝ)⌋₊) - (Int.ofNat ⌊((Q9:ℕ):ℝ)*x/(q.1:ℝ)⌋₊)))

/-- Real floor of a quotient equals the `Nat` quotient. -/
lemma nat_floor_nat_div (a b : ℕ) : ⌊((a:ℝ))/((b:ℝ))⌋₊ = a / b := by
  by_cases hb : b = 0
  · subst hb; simp
  · have hb0 : (0:ℝ) < (b:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hb)
    rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ (a:ℝ)/(b:ℝ))]
    constructor
    · rw [le_div_iff₀ hb0]
      have h := Nat.div_mul_le_self a b
      have hc : ((((a/b)*b : ℕ)):ℝ) ≤ (a:ℝ) := by exact_mod_cast h
      push_cast at hc
      linarith [hc]
    · rw [div_lt_iff₀ hb0]
      have hmod : a % b < b := Nat.mod_lt a (by omega)
      have hdm : b*(a/b) + a%b = a := Nat.div_add_mod a b
      have hc : (((b*(a/b) + a%b : ℕ)):ℝ) = (a:ℝ) := by exact_mod_cast hdm
      have hmodR : ((a%b : ℕ):ℝ) < (b:ℝ) := by exact_mod_cast hmod
      push_cast at hc ⊢
      linarith [hc, hmodR]

/-- Remainder bound for multiples of a divisor. -/
lemma nat_mod_le_of_dvd (a b d : ℕ) (hb : 0 < b) (_hd0 : 0 < d)
    (hdb : d ∣ b) (hda : d ∣ a) : a % b ≤ b - d := by
  have hdvdmod : d ∣ a % b := (Nat.dvd_mod_iff hdb).mpr hda
  by_contra hlt
  have hlt' : b - d < a % b := lt_of_not_ge hlt
  have hmod0 : a % b < b := Nat.mod_lt a hb
  have hsub : d ∣ b - a % b := Nat.dvd_sub hdb hdvdmod
  have hmod : a % b < b := Nat.mod_lt a hb
  have hpos : 0 < b - a % b := by omega
  have hlt2 : b - a % b < d := by omega
  have hle := Nat.le_of_dvd hpos hsub
  omega

/-- Floors at multiples match grid floors for `m ∣ 210`. -/
lemma floor_grid_match (C L : ℕ) (hC : 0 < C) (hL : 0 < L) (m : ℕ) (hm : m ∣ 210)
    (hCmL : C ∣ m * L) (x : ℝ) (hx : 0 ≤ x) :
    ⌊((C:ℕ):ℝ)*x/(m:ℝ)⌋₊ = C*⌊((L:ℕ):ℝ)*x⌋₊/(m*L) := by
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm (by norm_num)
  have hmL0 : 0 < m*L := Nat.mul_pos hm0 hL
  have hm0R : (m:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm0)
  have hL0R : (L:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  have hmL0R : ((m*L:ℕ):ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hmL0)
  have hfl : (((⌊((L:ℕ):ℝ)*x⌋₊ : ℕ)):ℝ) ≤ (L:ℝ)*x := Nat.floor_le (by positivity)
  have hlt : (L:ℝ)*x < (((⌊((L:ℕ):ℝ)*x⌋₊ : ℕ)):ℝ)+1 := Nat.lt_floor_add_one _
  set s : ℝ := (L:ℝ)*x - ⌊((L:ℕ):ℝ)*x⌋₊ with hs
  have hs0 : 0 ≤ s := by linarith [hfl]
  have hs1 : s < 1 := by linarith [hlt]
  have hCj : C*⌊((L:ℕ):ℝ)*x⌋₊
      = (m*L)*(C*⌊((L:ℕ):ℝ)*x⌋₊/(m*L)) + C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) :=
    (Nat.div_add_mod _ _).symm
  have hmod_le : C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) ≤ m*L - C :=
    nat_mod_le_of_dvd _ _ _ hmL0 hC hCmL (Nat.dvd_mul_right C _)
  have hCmL' : C ≤ m*L := Nat.le_of_dvd hmL0 hCmL
  have hfrac_lt : ((C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) : ℕ):ℝ) + (C:ℝ)*s < ((m*L : ℕ):ℝ) := by
    have h1 : ((C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) : ℕ):ℝ) ≤ ((m*L - C : ℕ):ℝ) := by
      exact_mod_cast hmod_le
    rw [Nat.cast_sub hCmL'] at h1
    have hC0 : (0:ℝ) < C := by exact_mod_cast hC
    have hsC : (C:ℝ)*s < (C:ℝ) := by
      have h := mul_lt_mul_of_pos_left hs1 hC0
      simpa using h
    linarith [h1, hsC]
  have hxeq : x = ((((⌊((L:ℕ):ℝ)*x⌋₊ : ℕ):ℝ) + s)) / (L:ℝ) := by
    rw [hs]
    field_simp
    ring
  have e1 : ((C:ℕ):ℝ)*x/(m:ℝ)
      = ((((C*⌊((L:ℕ):ℝ)*x⌋₊ : ℕ):ℝ) + (C:ℝ)*s)) / ((m*L : ℕ):ℝ) := by
    conv_lhs => rw [hxeq]
    push_cast
    field_simp
  have e2 : ((((C*⌊((L:ℕ):ℝ)*x⌋₊ : ℕ):ℝ) + (C:ℝ)*s)) / ((m*L : ℕ):ℝ)
      = (((C*⌊((L:ℕ):ℝ)*x⌋₊/(m*L) : ℕ)):ℝ)
        + ((((C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) : ℕ)):ℝ) + (C:ℝ)*s) / ((m*L : ℕ):ℝ) := by
    have hCjR : ((C*⌊((L:ℕ):ℝ)*x⌋₊ : ℕ):ℝ)
        = ((m*L : ℕ):ℝ) * (((C*⌊((L:ℕ):ℝ)*x⌋₊/(m*L) : ℕ)):ℝ)
          + ((C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) : ℕ):ℝ) := by exact_mod_cast hCj
    field_simp
    linarith [hCjR]
  rw [e1, e2, Nat.floor_eq_iff (by positivity :
    (0:ℝ) ≤ (((C*⌊((L:ℕ):ℝ)*x⌋₊/(m*L) : ℕ)):ℝ)
      + ((((C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) : ℕ)):ℝ) + (C:ℝ)*s) / ((m*L : ℕ):ℝ))]
  constructor
  · -- N ≤ N + frac
    have hnn : (0:ℝ) ≤ ((((C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) : ℕ)):ℝ) + (C:ℝ)*s)
        / ((m*L : ℕ):ℝ) := by positivity
    linarith [hnn]
  · -- N + frac < N + 1
    have hlt1 : ((((C*⌊((L:ℕ):ℝ)*x⌋₊%(m*L) : ℕ)):ℝ) + (C:ℝ)*s)
        / ((m*L : ℕ):ℝ) < 1 := by
      rw [div_lt_one (by exact_mod_cast hmL0 : (0:ℝ) < ((m*L:ℕ):ℝ))]
      linarith [hfrac_lt]
    linarith [hlt1]

-- One-period shift of a single div term. Needs m ∣ C (true for C ∈ {2100,1890,210}
-- when m ∣ 210, since 210 ∣ C).
/-- One-period shift identity for a single div term. -/
lemma div_shift189 (C m : ℕ) (hmC : m ∣ C) (hm0 : 0 < m) (j : ℕ) :
    (C*(j+18900))/(m*18900) = C*j/(m*18900) + C/m := by
  have hdm : C/m*m = C := Nat.div_mul_cancel hmC
  have hC : C*(j+18900) = C*j + (C/m)*(m*18900) := by
    have hK : (C/m)*(m*18900) = C*18900 := by
      calc (C/m)*(m*18900) = (C/m*m)*18900 := by ring
        _ = C*18900 := by rw [hdm]
    rw [hK]; ring
  rw [hC, Nat.add_mul_div_right _ _ (Nat.mul_pos hm0 (by norm_num))]

-- G9 is 18900-periodic: each C/m shift is integral and 10-9-1 cancels.
/-- `G9` is invariant under shifting by one period `18900`. -/
lemma G9_shift (j : ℕ) : G9 (j + 18900) = G9 j := by
  have hterm : ∀ q ∈ w9.toFinset, G9term q (j+18900) = G9term q j := by
    intro q hq
    have hqmem : q ∈ w9 := List.mem_toFinset.mp hq
    have hm : q.1 ∣ 210 := by rw [← Q9_eq]; exact w9_dvd q hqmem
    have hm0 : 0 < q.1 := w9_pos q hqmem
    have ⟨t, ht⟩ := hm
    have h210 : 210/q.1 = t := by rw [ht]; exact Nat.mul_div_cancel_left _ hm0
    have h9 : 9*210/q.1 = 9*t := by
      rw [ht, show 9*(q.1*t) = q.1*(9*t) by ring]
      exact Nat.mul_div_cancel_left _ hm0
    have h10 : 10*210/q.1 = 10*t := by
      rw [ht, show 10*(q.1*t) = q.1*(10*t) by ring]
      exact Nat.mul_div_cancel_left _ hm0
    have hK : ((10*210/q.1 : ℕ):ℤ) = ((9*210/q.1 : ℕ):ℤ) + ((210/q.1 : ℕ):ℤ) := by
      rw [h10, h9, h210]; push_cast; ring
    have e10 := div_shift189 (10*210) q.1 (dvd_trans hm (Nat.dvd_mul_left 210 10)) hm0 j
    have e9 := div_shift189 (9*210) q.1 (dvd_trans hm (Nat.dvd_mul_left 210 9)) hm0 j
    have e1 := div_shift189 210 q.1 hm hm0 j
    unfold G9term
    rw [e10, e9, e1]
    simp only [Nat.cast_add]
    linear_combination q.2 * hK
  have e1 := map_sum_toFinset w9 w9_nodup (fun q => G9term q (j+18900))
  have e2 := map_sum_toFinset w9 w9_nodup (fun q => G9term q j)
  unfold G9
  rw [e1, e2]
  exact Finset.sum_congr rfl hterm

/-- Iterated form of grid periodicity. -/
lemma G9_period_iter (o r : ℕ) : G9 (18900*o + r) = G9 r := by
  induction o with
  | zero => simp
  | succ o ih =>
    rw [show 18900*(o+1)+r = (18900*o+r)+18900 by ring, G9_shift, ih]

/-- `G9 j` depends only on `j % 18900`. -/
lemma G9_eq_mod (j : ℕ) : G9 j = G9 (j % 18900) := by
  conv_lhs => rw [← Nat.div_add_mod j 18900]
  exact G9_period_iter _ _

-- Continuous-to-grid identity via floor_grid_match (L = 18900).
/-- The continuous `G9r` equals the grid `G9` at `⌊18900 * x⌋₊`. -/
lemma G9r_eq_grid (x : ℝ) (hx : 0 ≤ x) : G9r x = G9 ⌊(18900:ℝ)*x⌋₊ := by
  have hterm : ∀ q ∈ w9.toFinset,
      q.2 * ((Int.ofNat ⌊((10*Q9:ℕ):ℝ)*x/(q.1:ℝ)⌋₊)
        - (Int.ofNat ⌊((9*Q9:ℕ):ℝ)*x/(q.1:ℝ)⌋₊)
        - (Int.ofNat ⌊((Q9:ℕ):ℝ)*x/(q.1:ℝ)⌋₊))
      = G9term q ⌊(18900:ℝ)*x⌋₊ := by
    intro q hq
    have hqmem : q ∈ w9 := List.mem_toFinset.mp hq
    have hm : q.1 ∣ 210 := by rw [← Q9_eq]; exact w9_dvd q hqmem
    have e10 := floor_grid_match (10*Q9) 18900 (by rw [Q9_eq]; norm_num) (by norm_num)
      q.1 hm ⟨q.1*9, by rw [Q9_eq]; ring⟩ x hx
    have e9 := floor_grid_match (9*Q9) 18900 (by rw [Q9_eq]; norm_num) (by norm_num)
      q.1 hm ⟨q.1*10, by rw [Q9_eq]; ring⟩ x hx
    have e1 := floor_grid_match Q9 18900 (by rw [Q9_eq]; norm_num) (by norm_num)
      q.1 hm ⟨q.1*90, by rw [Q9_eq]; ring⟩ x hx
    rw [e10, e9, e1]
    unfold G9term
    simp only [Int.ofNat_eq_natCast, Q9_eq, Nat.cast_ofNat]
  unfold G9r G9
  rw [map_sum_toFinset w9 w9_nodup (fun q => G9term q ⌊(18900:ℝ)*x⌋₊)]
  exact Finset.sum_congr rfl hterm

-- Small-grid certificates.
/-- `G9` vanishes below `9`. -/
theorem G9_zero9 : ∀ j < 9, G9 j = 0 := by decide
/-- `G9 9 = 1`. -/
theorem G9_at9 : G9 9 = 1 := by decide
/-- `G9 ≤ 1` below `10`. -/
theorem G9_small_le1 : ∀ j < 10, G9 j ≤ 1 := by decide

-- Consequences of the grid certificate for the continuous function.
/-- Global bound `G9r x ≤ 3` for `x ≥ 0`. -/
theorem G9r_le3 (x : ℝ) (hx : 0 ≤ x) : G9r x ≤ 3 := by
  rw [G9r_eq_grid x hx, G9_eq_mod]
  exact M9_le _ (Nat.mod_lt _ (by norm_num))

/-- `G9r` vanishes on `[0, 1 / 2100)`. -/
theorem G9r_vanish (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 1 / ((10 * Q9 : ℕ) : ℝ)) :
    G9r x = 0 := by
  have h10 : ((10 * Q9 : ℕ) : ℝ) = 2100 := by rw [Q9_eq]; norm_num
  rw [h10] at hx
  rw [G9r_eq_grid x hx0]
  have hj : ⌊(18900 : ℝ) * x⌋₊ < 9 := by
    rw [Nat.floor_lt (mul_nonneg (by norm_num) hx0)]
    push_cast
    linarith
  exact G9_zero9 _ hj

/-- Level `G9r ≥ 1` forces `x ≥ 279 / 18900`. -/
theorem G9r_level1 (x : ℝ) (hx : 1 / ((9 * Q9 : ℕ) : ℝ) ≤ x) (h : 1 ≤ G9r x) :
    (279 : ℝ) / 18900 ≤ x := by
  have h9 : ((9 * Q9 : ℕ) : ℝ) = 1890 := by rw [Q9_eq]; norm_num
  rw [h9] at hx
  have hx0 : 0 ≤ x := by linarith
  rw [G9r_eq_grid x hx0, G9_eq_mod] at h
  set r := ⌊(18900 : ℝ) * x⌋₊ % 18900 with hr
  have hj10 : 10 ≤ ⌊(18900 : ℝ) * x⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith
  have hdecomp := Nat.div_add_mod ⌊(18900 : ℝ) * x⌋₊ 18900
  -- Either r ≥ 10 (jmin route) or r = 9 with quotient ≥ 1 (j ≥ 18909).
  have key : 279 ≤ ⌊(18900 : ℝ) * x⌋₊ := by
    by_cases hr10 : 10 ≤ r
    · have h279 : 279 ≤ r := by
        by_contra hc
        push Not at hc
        have hlt := jmin1.2 r hr10 hc
        omega
      have hmod : r ≤ ⌊(18900 : ℝ) * x⌋₊ := Nat.mod_le _ _
      omega
    · push Not at hr10
      have hr9 : r = 9 := by
        by_contra hc
        have hr9' : r < 9 := by omega
        have hz := G9_zero9 r hr9'
        omega
      omega
  have hfloor : ((⌊(18900 : ℝ) * x⌋₊ : ℕ):ℝ) ≤ (18900 : ℝ) * x :=
    Nat.floor_le (mul_nonneg (by norm_num) hx0)
  have hkeyR : (279 : ℝ) ≤ ((⌊(18900 : ℝ) * x⌋₊ : ℕ):ℝ) := by exact_mod_cast key
  linarith

/-- Level `G9r ≥ 2` forces `x ≥ 657 / 18900`. -/
theorem G9r_level2 (x : ℝ) (hx : 1 / ((9 * Q9 : ℕ) : ℝ) ≤ x) (h : 2 ≤ G9r x) :
    (657 : ℝ) / 18900 ≤ x := by
  have h9 : ((9 * Q9 : ℕ) : ℝ) = 1890 := by rw [Q9_eq]; norm_num
  rw [h9] at hx
  have hx0 : 0 ≤ x := by linarith
  rw [G9r_eq_grid x hx0, G9_eq_mod] at h
  set r := ⌊(18900 : ℝ) * x⌋₊ % 18900 with hr
  have key : 657 ≤ ⌊(18900 : ℝ) * x⌋₊ := by
    by_cases hr10 : 10 ≤ r
    · have h657 : 657 ≤ r := by
        by_contra hc
        push Not at hc
        have hlt := jmin2.2 r hr10 hc
        omega
      have hmod : r ≤ ⌊(18900 : ℝ) * x⌋₊ := Nat.mod_le _ _
      omega
    · push Not at hr10
      have hle := G9_small_le1 r hr10
      omega
  have hfloor : ((⌊(18900 : ℝ) * x⌋₊ : ℕ):ℝ) ≤ (18900 : ℝ) * x :=
    Nat.floor_le (mul_nonneg (by norm_num) hx0)
  have hkeyR : (657 : ℝ) ≤ ((⌊(18900 : ℝ) * x⌋₊ : ℕ):ℝ) := by exact_mod_cast key
  linarith

/-- Level `G9r ≥ 3` forces `x ≥ 963 / 18900`. -/
theorem G9r_level3 (x : ℝ) (hx : 1 / ((9 * Q9 : ℕ) : ℝ) ≤ x) (h : 3 ≤ G9r x) :
    (963 : ℝ) / 18900 ≤ x := by
  have h9 : ((9 * Q9 : ℕ) : ℝ) = 1890 := by rw [Q9_eq]; norm_num
  rw [h9] at hx
  have hx0 : 0 ≤ x := by linarith
  rw [G9r_eq_grid x hx0, G9_eq_mod] at h
  set r := ⌊(18900 : ℝ) * x⌋₊ % 18900 with hr
  have key : 963 ≤ ⌊(18900 : ℝ) * x⌋₊ := by
    by_cases hr10 : 10 ≤ r
    · have h963 : 963 ≤ r := by
        by_contra hc
        push Not at hc
        have hlt := jmin3.2 r hr10 hc
        omega
      have hmod : r ≤ ⌊(18900 : ℝ) * x⌋₊ := Nat.mod_le _ _
      omega
    · push Not at hr10
      have hle := G9_small_le1 r hr10
      omega
  have hfloor : ((⌊(18900 : ℝ) * x⌋₊ : ℕ):ℝ) ≤ (18900 : ℝ) * x :=
    Nat.floor_le (mul_nonneg (by norm_num) hx0)
  have hkeyR : (963 : ℝ) ≤ ((⌊(18900 : ℝ) * x⌋₊ : ℕ):ℝ) := by exact_mod_cast key
  linarith

/-- Real floors of `Nat` quotients as integer casts. -/
lemma intFloor_cast (t d : ℕ) :
    (Int.ofNat ⌊((t : ℕ) : ℝ) / ((d : ℕ) : ℝ)⌋₊ : ℤ) = ((t / d : ℕ) : ℤ) := by
  rw [nat_floor_nat_div]
  exact Int.ofNat_eq_natCast _

-- Nat divs in Legendre sums equal the G9r floors.
/-- `N10` Legendre terms as `G9r` floors. -/
lemma floor_N10 {m n p j : ℕ} (hm : 1 ≤ m) (hd : m ∣ Q9) (hp2 : 2 ≤ p) :
    ((N10m m n / p ^ j : ℕ) : ℤ)
      = Int.ofNat ⌊((10*Q9:ℕ):ℝ)*((n : ℝ) / (((p ^ j : ℕ)) : ℝ))/((m : ℕ) : ℝ)⌋₊ := by
  have hp0 : p ≠ 0 := by omega
  have hmp : m * p ^ j ≠ 0 := mul_ne_zero (by omega) (pow_ne_zero j hp0)
  have hmR : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hpjR : ((((p ^ j : ℕ))) : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero j hp0)
  have hdiv : N10m m n / p ^ j = 10 * Q9 * n / (m * p ^ j) := by
    rw [N10_eq hm hd, Nat.div_div_eq_div_mul]
  rw [hdiv]
  have he : ((10*Q9:ℕ):ℝ)*((n : ℝ) / (((p ^ j : ℕ)) : ℝ))/((m : ℕ) : ℝ)
      = (((10 * Q9 * n : ℕ)) : ℝ) / (((m * p ^ j : ℕ)) : ℝ) := by
    push_cast
    field_simp
  rw [he]
  exact (intFloor_cast _ _).symm

/-- `N9` Legendre terms as `G9r` floors. -/
lemma floor_N9 {m n p j : ℕ} (hm : 1 ≤ m) (hd : m ∣ Q9) (hp2 : 2 ≤ p) :
    ((N9m m n / p ^ j : ℕ) : ℤ)
      = Int.ofNat ⌊((9*Q9:ℕ):ℝ)*((n : ℝ) / (((p ^ j : ℕ)) : ℝ))/((m : ℕ) : ℝ)⌋₊ := by
  have hp0 : p ≠ 0 := by omega
  have hmp : m * p ^ j ≠ 0 := mul_ne_zero (by omega) (pow_ne_zero j hp0)
  have hmR : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hpjR : ((((p ^ j : ℕ))) : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero j hp0)
  have hdiv : N9m m n / p ^ j = 9 * Q9 * n / (m * p ^ j) := by
    rw [N9_eq hm hd, Nat.div_div_eq_div_mul]
  rw [hdiv]
  have he : ((9*Q9:ℕ):ℝ)*((n : ℝ) / (((p ^ j : ℕ)) : ℝ))/((m : ℕ) : ℝ)
      = (((9 * Q9 * n : ℕ)) : ℝ) / (((m * p ^ j : ℕ)) : ℝ) := by
    push_cast
    field_simp
  rw [he]
  exact (intFloor_cast _ _).symm

/-- `N1` Legendre terms as `G9r` floors. -/
lemma floor_N1 {m n p j : ℕ} (hm : 1 ≤ m) (hd : m ∣ Q9) (hp2 : 2 ≤ p) :
    ((N1m m n / p ^ j : ℕ) : ℤ)
      = Int.ofNat ⌊((Q9:ℕ):ℝ)*((n : ℝ) / (((p ^ j : ℕ)) : ℝ))/((m : ℕ) : ℝ)⌋₊ := by
  have hp0 : p ≠ 0 := by omega
  have hmp : m * p ^ j ≠ 0 := mul_ne_zero (by omega) (pow_ne_zero j hp0)
  have hmR : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hpjR : ((((p ^ j : ℕ))) : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero j hp0)
  have hdiv : N1m m n / p ^ j = Q9 * n / (m * p ^ j) := by
    rw [N1_eq hm hd, Nat.div_div_eq_div_mul]
  rw [hdiv]
  have he : ((Q9:ℕ):ℝ)*((n : ℝ) / (((p ^ j : ℕ)) : ℝ))/((m : ℕ) : ℝ)
      = (((Q9 * n : ℕ)) : ℝ) / (((m * p ^ j : ℕ)) : ℝ) := by
    push_cast
    field_simp
  rw [he]
  exact (intFloor_cast _ _).symm

-- Legendre in integers.
/-- Legendre formula for factorial valuations as integer sums. -/
lemma legendre_sum9 {N p b : ℕ} (hp : p.Prime) (h : Nat.log p N < b) :
    (((N)!.factorization p : ℤ)) = ∑ j ∈ Finset.Ico 1 b, ((N / p ^ j : ℕ) : ℤ) := by
  have hnat := Nat.factorization_factorial hp h
  exact_mod_cast hnat

-- Valuation of a ratio factor in integers (no truncation).
/-- Valuation of a ratio factor as a difference of valuations. -/
lemma vp_ratio9 {m n p : ℕ} (hm1 : 1 ≤ m) (hd : m ∣ Q9) :
    ((ratio9 m n).factorization p : ℤ)
      = (((N10m m n)!.factorization p : ℤ) - ((N9m m n)!.factorization p : ℤ)
        - ((N1m m n)!.factorization p : ℤ)) := by
  have hdvd := ratio9_dvd m n hm1 hd
  have h9 : (N9m m n)! ≠ 0 := Nat.factorial_ne_zero _
  have h1 : (N1m m n)! ≠ 0 := Nat.factorial_ne_zero _
  have hpos1 : (N9m m n)! * (N1m m n)! ≠ 0 := mul_ne_zero h9 h1
  have hpos2 : (N10m m n)! ≠ 0 := Nat.factorial_ne_zero _
  have hfact := Nat.factorization_div hdvd
  have hle : ((N9m m n)! * (N1m m n)!).factorization
      ≤ ((N10m m n)!).factorization :=
    (Nat.factorization_le_iff_dvd hpos1 hpos2).mpr hdvd
  rw [Finsupp.le_def] at hle
  have hle_p := hle p
  have hmul := Nat.factorization_mul h9 h1
  unfold ratio9
  rw [hfact, Finsupp.tsub_apply, Nat.cast_sub hle_p, hmul, Finsupp.add_apply,
    Nat.cast_add]
  ring

-- Single-factor valuation term.
/-- Single-factor `p`-adic valuation contribution. -/
def nu9term (q : ℕ × ℤ) (p n : ℕ) : ℤ :=
  q.2 * (((N10m q.1 n)!.factorization p : ℤ)
    - ((N9m q.1 n)!.factorization p : ℤ)
    - ((N1m q.1 n)!.factorization p : ℤ))

-- Total p-adic valuation of F(n).
/-- Total `p`-adic valuation of the weighted product `F_9(n)`. -/
def nu9 (p n : ℕ) : ℤ :=
  w9.toFinset.sum (fun q : ℕ × ℤ => nu9term q p n)

-- Vanishing of G9r(n/p^j) for large p^j.
/-- `G9r (n / p ^ j)` vanishes for `p ^ j > 10 * Q9 * n`. -/
lemma G9r_vanish_of {n p j : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (h : 10 * Q9 * n < p ^ j) : G9r ((n : ℝ) / (((p ^ j : ℕ)) : ℝ)) = 0 := by
  apply G9r_vanish
  · positivity
  · have hpj : 0 < p ^ j := pow_pos hp.pos j
    have hpos : (0 : ℝ) < ((((p ^ j : ℕ))) : ℝ) := by exact_mod_cast hpj
    have hX : (0 : ℝ) < ((((10 * Q9 : ℕ))) : ℝ) := by
      have hQ : 0 < Q9 := Q9_pos
      have hne : 10 * Q9 ≠ 0 := mul_ne_zero (by norm_num) (by omega)
      exact_mod_cast (Nat.pos_of_ne_zero hne)
    have hcast : ((((10 * Q9 * n : ℕ))) : ℝ) < ((((p ^ j : ℕ))) : ℝ) := by
      exact_mod_cast h
    have heq : ((((10 * Q9 * n : ℕ))) : ℝ) = ((((10 * Q9 : ℕ))) : ℝ) * (n : ℝ) := by
      push_cast
      ring
    rw [heq] at hcast
    rw [div_lt_div_iff₀ hpos hX]
    have hcomm : (n : ℝ) * ((((10 * Q9 : ℕ))) : ℝ)
        = ((((10 * Q9 : ℕ))) : ℝ) * (n : ℝ) := by ring
    linarith [hcast, hcomm]

-- The ν-identity: total valuation = Σ_j G9r(n/p^j).
/-- Valuation identity: `nu9` is a sum of `G9r` values. -/
lemma nu9_eq_sum_G {p n b : ℕ} (hp : p.Prime)
    (hb : Nat.log p (10 * Q9 * n) < b) :
    nu9 p n = ∑ j ∈ Finset.Ico 1 b, G9r ((n : ℝ) / (((p ^ j : ℕ)) : ℝ)) := by
  classical
  have hp2 : 2 ≤ p := hp.two_le
  have hlog10 : ∀ q ∈ w9.toFinset, Nat.log p (N10m q.1 n) < b :=
    fun q _ => lt_of_le_of_lt (Nat.log_mono_right N10_le) hb
  have hlog9 : ∀ q ∈ w9.toFinset, Nat.log p (N9m q.1 n) < b :=
    fun q _ => lt_of_le_of_lt (Nat.log_mono_right N9_le) hb
  have hlog1 : ∀ q ∈ w9.toFinset, Nat.log p (N1m q.1 n) < b :=
    fun q _ => lt_of_le_of_lt (Nat.log_mono_right N1_le) hb
  unfold nu9
  have hterm : ∀ q ∈ w9.toFinset, nu9term q p n
      = ∑ j ∈ Finset.Ico 1 b, q.2 * ((((N10m q.1 n / p ^ j : ℕ)) : ℤ)
        - (((N9m q.1 n / p ^ j : ℕ)) : ℤ) - (((N1m q.1 n / p ^ j : ℕ)) : ℤ)) := by
    intro q hq
    unfold nu9term
    rw [legendre_sum9 hp (hlog10 q hq), legendre_sum9 hp (hlog9 q hq),
      legendre_sum9 hp (hlog1 q hq), mul_sub, mul_sub,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  unfold G9r
  apply Finset.sum_congr rfl
  intro q hq
  have hmem : q ∈ w9 := List.mem_toFinset.mp hq
  have hm : 1 ≤ q.1 := w9_pos q hmem
  have hd : q.1 ∣ Q9 := w9_dvd q hmem
  rw [floor_N10 hm hd hp2, floor_N9 hm hd hp2, floor_N1 hm hd hp2]

-- For p^2 > 10Qn, only j = 1 contributes.
/-- For `p ^ 2 > 10 * Q9 * n`, only `j = 1` contributes. -/
lemma nu9_eq_single {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hbig : 10 * Q9 * n < p ^ 2) : nu9 p n = G9r ((n : ℝ) / (((p : ℕ)) : ℝ)) := by
  set b : ℕ := Nat.log p (10 * Q9 * n) + 2 with hb_def
  have hb : Nat.log p (10 * Q9 * n) < b := by omega
  rw [nu9_eq_sum_G hp hb]
  have hsplit : Finset.Ico 1 b = insert 1 (Finset.Ico 2 b) := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega)]
  have hzero : ∑ j ∈ Finset.Ico 2 b, G9r ((n : ℝ) / (((p ^ j : ℕ)) : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hpow : p ^ 2 ≤ p ^ j := pow_le_pow_right₀ hp.pos hj.1
    have h : 10 * Q9 * n < p ^ j := lt_of_lt_of_le hbig hpow
    exact G9r_vanish_of hp hn h
  rw [hzero, add_zero, pow_one]

/-- `10 * Q9 * n = 2100 * n`. -/
lemma U9_10Q9 (n : ℕ) : 10 * Q9 * n = 2100 * n := by rw [Q9_eq]

/-- Logarithm of `K` via its prime factorization. -/
lemma U9_log_fact (K : ℕ) (hK : K ≠ 0) :
    Real.log ((K : ℕ) : ℝ) =
      ∑ p ∈ K.factorization.support, ((K.factorization p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
  have hprod := Nat.prod_factorization_pow_eq_self hK
  have hcast : ((K : ℕ) : ℝ)
      = ∏ p ∈ K.factorization.support, ((((p : ℕ)) : ℝ) ^ K.factorization p) := by
    have h2 := congrArg (Nat.cast : ℕ → ℝ) hprod
    have hdef : K.factorization.prod (fun p e => p ^ e)
        = ∏ p ∈ K.factorization.support, p ^ K.factorization p := rfl
    rw [hdef, Nat.cast_prod] at h2
    simpa using h2.symm
  rw [hcast, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Real.log_pow]
  · intro p hp
    have hpmem : p ∈ K.primeFactors := Nat.support_factorization K ▸ hp
    have hpp := Nat.prime_of_mem_primeFactors hpmem
    have hp0 : (p : ℕ) ≠ 0 := ne_of_gt hpp.pos
    exact pow_ne_zero _ (by exact_mod_cast hp0)

/-- Ratio factors involve only primes `≤ 2100 * n`. -/
lemma U9_supp_sub (q : ℕ × ℤ) (hq : q ∈ w9) (n : ℕ) :
    (ratio9 q.1 n).factorization.support ⊆ Nat.primesBelow (2100 * n + 1) := by
  intro p hp
  have hpmem : p ∈ (ratio9 q.1 n).primeFactors :=
    Nat.support_factorization _ ▸ hp
  have hpp := Nat.prime_of_mem_primeFactors hpmem
  have hdvdR : p ∣ ratio9 q.1 n := Nat.dvd_of_mem_primeFactors hpmem
  have hm1 : 1 ≤ q.1 := w9_pos q hq
  have hd : q.1 ∣ Q9 := w9_dvd q hq
  have hRdvd : ratio9 q.1 n ∣ (N10m q.1 n)! := by
    have h := ratio9_dvd q.1 n hm1 hd
    exact ⟨_, (Nat.div_mul_cancel h).symm⟩
  have hpF : p ∣ (N10m q.1 n)! := dvd_trans hdvdR hRdvd
  have hleN : p ≤ N10m q.1 n := (Nat.Prime.dvd_factorial hpp).mp hpF
  have hleX : p ≤ 2100 * n := by
    have h := N10_le (m := q.1) (n := n)
    rw [Q9_eq] at h
    omega
  rw [Nat.mem_primesBelow]
  exact ⟨by omega, hpp⟩

/-- Single valuation term against the ratio factorization. -/
lemma U9_nu9term_eq (q : ℕ × ℤ) (p n : ℕ) (hm1 : 1 ≤ q.1) (hd : q.1 ∣ Q9) :
    ((nu9term q p n : ℤ) : ℝ)
      = (q.2 : ℝ) * (((ratio9 q.1 n).factorization p : ℕ) : ℝ) := by
  unfold nu9term
  have h := vp_ratio9 (m := q.1) (n := n) (p := p) hm1 hd
  rw [← h, Int.cast_mul]
  simp

/-- Vanishing single valuation term off the support. -/
lemma U9_nu9term_zero (q : ℕ × ℤ) (p n : ℕ) (hm1 : 1 ≤ q.1) (hd : q.1 ∣ Q9)
    (h0 : (ratio9 q.1 n).factorization p = 0) : nu9term q p n = 0 := by
  unfold nu9term
  have h := vp_ratio9 (m := q.1) (n := n) (p := p) hm1 hd
  rw [h0, Nat.cast_zero] at h
  rw [← h, mul_zero]

/-- One weighted log-factor as a prime sum. -/
lemma U9_q_expand (q : ℕ × ℤ) (hq : q ∈ w9) (n : ℕ) (hn : 1 ≤ n) :
    (q.2 : ℝ) * Real.log ((ratio9 q.1 n : ℕ) : ℝ)
      = ∑ p ∈ Nat.primesBelow (2100 * n + 1),
        ((nu9term q p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
  have hm1 : 1 ≤ q.1 := w9_pos q hq
  have hd : q.1 ∣ Q9 := w9_dvd q hq
  have hRne : ratio9 q.1 n ≠ 0 := ne_of_gt (ratio9_pos _ _ hn hm1 hd)
  have hterm : ∀ p ∈ (ratio9 q.1 n).factorization.support,
      (q.2 : ℝ) * (((((ratio9 q.1 n).factorization p : ℕ)) : ℝ) * Real.log ((p : ℕ) : ℝ))
        = (((nu9term q p n : ℤ)) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
    intro p _
    rw [U9_nu9term_eq q p n hm1 hd]
    ring
  calc (q.2 : ℝ) * Real.log ((ratio9 q.1 n : ℕ) : ℝ)
      = ∑ p ∈ (ratio9 q.1 n).factorization.support,
          (q.2 : ℝ) * (((((ratio9 q.1 n).factorization p : ℕ)) : ℝ)
            * Real.log ((p : ℕ) : ℝ)) := by
        rw [U9_log_fact _ hRne, Finset.mul_sum]
    _ = ∑ p ∈ (ratio9 q.1 n).factorization.support,
          (((nu9term q p n : ℤ)) : ℝ) * Real.log ((p : ℕ) : ℝ) :=
        Finset.sum_congr rfl hterm
    _ = ∑ p ∈ Nat.primesBelow (2100 * n + 1),
          (((nu9term q p n : ℤ)) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
        apply Finset.sum_subset (U9_supp_sub q hq n)
        intro p _ hpnot
        have h0 : (ratio9 q.1 n).factorization p = 0 :=
          Finsupp.notMem_support_iff.mp hpnot
        rw [U9_nu9term_zero q p n hm1 hd h0, Int.cast_zero, zero_mul]

/-- `logF9` as a weighted prime-logarithm sum. -/
lemma U9_bridge (n : ℕ) (hn : 1 ≤ n) :
    logF9 n = ∑ p ∈ Nat.primesBelow (2100 * n + 1),
      ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
  classical
  unfold logF9
  have hexp : ∀ q ∈ w9.toFinset,
      (q.2 : ℝ) * Real.log ((ratio9 q.1 n : ℕ) : ℝ)
        = ∑ p ∈ Nat.primesBelow (2100 * n + 1),
          (((nu9term q p n : ℤ)) : ℝ) * Real.log ((p : ℕ) : ℝ) :=
    fun q hq => U9_q_expand q (List.mem_toFinset.mp hq) n hn
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  unfold nu9
  rw [Int.cast_sum, Finset.sum_mul]

/-- Logarithms of primes are nonnegative. -/
lemma U9_logp_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log ((p : ℕ) : ℝ) := by
  have h1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp.two_le
    linarith
  exact Real.log_nonneg h1

/-- Integer `G9r` values are bounded by their `toNat` cast. -/
lemma U9_G_toNat (x : ℝ) : ((G9r x : ℤ) : ℝ) ≤ ((((G9r x).toNat : ℕ)) : ℝ) := by
  rcases le_total (G9r x) 0 with h | h
  · rw [Int.toNat_eq_zero.mpr h, Nat.cast_zero]
    exact_mod_cast h
  · have e : ((((G9r x).toNat : ℕ)) : ℝ) = ((G9r x : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
    rw [e]

/-- Truncated `G9r` values are at most `3`. -/
lemma U9_toNat_le3 (x : ℝ) (hx : 0 ≤ x) : (G9r x).toNat ≤ 3 := by
  have h := G9r_le3 x hx
  have h2 := Int.toNat_le_toNat h
  have h3 : (3 : ℤ).toNat = 3 := rfl
  rwa [h3] at h2

/-- Truncation lower bounds lift back to integers. -/
lemma U9_of_toNat {z : ℤ} {i : ℕ} (hi : 1 ≤ i) (h : i ≤ z.toNat) :
    (i : ℤ) ≤ z := by
  have hz : 0 ≤ z := by
    by_contra hc
    push Not at hc
    have h0 : z.toNat = 0 := Int.toNat_eq_zero.mpr (le_of_lt hc)
    omega
  have e : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz
  have h2 : ((i : ℕ) : ℤ) ≤ ((z.toNat : ℕ) : ℤ) := by exact_mod_cast h
  rwa [e] at h2

/-- Layer-cake decomposition of a truncated sum over levels `1..3`. -/
lemma U9_layercake (B : Finset ℕ) (M : ℕ → ℕ) (c : ℕ → ℝ)
    (hM : ∀ p ∈ B, M p ≤ 3) :
    ∑ p ∈ B, ((M p : ℕ) : ℝ) * c p
      = ∑ i ∈ Finset.Icc 1 3, ∑ p ∈ B.filter (fun p => i ≤ M p), c p := by
  classical
  have h1 : ∀ p ∈ B, ((M p : ℕ) : ℝ)
      = ∑ i ∈ Finset.Icc 1 3, (if i ≤ M p then (1 : ℝ) else 0) := by
    intro p hp
    have hMp3 := hM p hp
    have hfeq : (Finset.Icc 1 3).filter (fun i => i ≤ M p)
        = Finset.Icc 1 (M p) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    have hc : (Finset.Icc 1 (M p)).card = M p := by
      rw [Nat.card_Icc]
      omega
    calc ((M p : ℕ) : ℝ)
        = (((Finset.Icc 1 3).filter (fun i => i ≤ M p)).card : ℝ) := by
          rw [hfeq, hc]
      _ = ∑ i ∈ Finset.Icc 1 3, (if i ≤ M p then (1 : ℝ) else 0) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hMp : ∀ p ∈ B, ((M p : ℕ) : ℝ) * c p
      = ∑ i ∈ Finset.Icc 1 3, (if i ≤ M p then c p else 0) := by
    intro p hp
    calc ((M p : ℕ) : ℝ) * c p
        = (∑ i ∈ Finset.Icc 1 3, (if i ≤ M p then (1 : ℝ) else 0)) * c p := by
          rw [h1 p hp]
      _ = ∑ i ∈ Finset.Icc 1 3, (if i ≤ M p then c p else 0) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs with hi
          · ring
          · ring
  rw [Finset.sum_congr rfl hMp, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_filter]

/-- A level lower bound converts to a prime upper bound. -/
lemma U9_ple_of_G (n p : ℕ) (_hn : 1 ≤ n) (hp : p.Prime)
    (jm : ℝ) (hjm : 1 ≤ jm)
    (hlvl : jm / 18900 ≤ (n : ℝ) / ((p : ℕ) : ℝ)) :
    ((p : ℕ) : ℝ) ≤ 18900 * (n : ℝ) / jm := by
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.pos
  have hjm0 : (0 : ℝ) < jm := lt_of_lt_of_le zero_lt_one hjm
  have h18900 : (0 : ℝ) < 18900 := by norm_num
  have hcross : jm * ((p : ℕ) : ℝ) ≤ (n : ℝ) * 18900 := by
    have h1 : (jm / 18900) * ((p : ℕ) : ℝ) ≤ (n : ℝ) := (le_div_iff₀ hp0).mp hlvl
    have h2 : ((jm / 18900) * ((p : ℕ) : ℝ)) * 18900 ≤ (n : ℝ) * 18900 :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt h18900)
    have e : ((jm / 18900) * ((p : ℕ) : ℝ)) * 18900 = jm * ((p : ℕ) : ℝ) := by
      ring
    linarith [h2, e]
  rw [le_div_iff₀ hjm0]
  linarith [hcross]

/-- Primes `≤ 1890 * n` give `n / p ≥ 1 / 1890`. -/
lemma U9_xlo (n p : ℕ) (_hn : 1 ≤ n) (hp : p.Prime) (hle : p ≤ 1890 * n) :
    1 / (((9 * Q9 : ℕ)) : ℝ) ≤ (n : ℝ) / ((p : ℕ) : ℝ) := by
  have h9Q : (((9 * Q9 : ℕ)) : ℝ) = 1890 := by
    have hnat : (9 * Q9 : ℕ) = 1890 := by decide
    rw [hnat]
    norm_num
  rw [h9Q]
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.pos
  rw [le_div_iff₀ hp0]
  have hleR : ((p : ℕ) : ℝ) ≤ 1890 * (n : ℝ) := by exact_mod_cast hle
  linarith [hleR]

/-- Level-1 primes are at most `18900 * n / 279`. -/
lemma U9_ple1 (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime)
    (hle : p ≤ 1890 * n) (hG : (1 : ℤ) ≤ G9r ((n : ℝ) / ((p : ℕ) : ℝ))) :
    ((p : ℕ) : ℝ) ≤ 18900 * (n : ℝ) / 279 := by
  apply U9_ple_of_G n p hn hp 279 (by norm_num)
  exact G9r_level1 _ (U9_xlo n p hn hp hle) hG

/-- Level-2 primes are at most `18900 * n / 657`. -/
lemma U9_ple2 (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime)
    (hle : p ≤ 1890 * n) (hG : (2 : ℤ) ≤ G9r ((n : ℝ) / ((p : ℕ) : ℝ))) :
    ((p : ℕ) : ℝ) ≤ 18900 * (n : ℝ) / 657 := by
  apply U9_ple_of_G n p hn hp 657 (by norm_num)
  exact G9r_level2 _ (U9_xlo n p hn hp hle) hG

/-- Level-3 primes are at most `18900 * n / 963`. -/
lemma U9_ple3 (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime)
    (hle : p ≤ 1890 * n) (hG : (3 : ℤ) ≤ G9r ((n : ℝ) / ((p : ℕ) : ℝ))) :
    ((p : ℕ) : ℝ) ≤ 18900 * (n : ℝ) / 963 := by
  apply U9_ple_of_G n p hn hp 963 (by norm_num)
  exact G9r_level3 _ (U9_xlo n p hn hp hle) hG

/-- The primorial as a product over `primesBelow`. -/
lemma U9_primorial_eq (k : ℕ) :
    primorial k = ∏ p ∈ Nat.primesBelow (k + 1), p := by
  have hset : Nat.primesBelow (k + 1)
      = (Finset.range (k + 1)).filter (fun p => p.Prime) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primesBelow]
  unfold primorial
  rw [hset]

/-- Prime-log sum bounded by the `3.4` primorial estimate. -/
lemma U9_theta_le (Y : ℝ) (hY : 0 ≤ Y) :
    ∑ p ∈ Nat.primesBelow (⌊Y⌋₊ + 1), Real.log ((p : ℕ) : ℝ)
      ≤ Y * Real.log 3.4 := by
  classical
  have hpos : (0 : ℝ) < (((primorial ⌊Y⌋₊ : ℕ)) : ℝ) := by
    have h := primorial_pos ⌊Y⌋₊
    exact_mod_cast h
  have hprod : (∏ p ∈ Nat.primesBelow (⌊Y⌋₊ + 1), ((p : ℕ) : ℝ))
      = (((primorial ⌊Y⌋₊ : ℕ)) : ℝ) := by
    rw [← Nat.cast_prod, U9_primorial_eq]
  have hne : ∀ p ∈ Nat.primesBelow (⌊Y⌋₊ + 1), (((p : ℕ) : ℝ) ≠ 0) := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    have hp0 : p ≠ 0 := ne_of_gt hp.2.pos
    exact_mod_cast hp0
  have hlog : ∑ p ∈ Nat.primesBelow (⌊Y⌋₊ + 1), Real.log ((p : ℕ) : ℝ)
      = Real.log (((primorial ⌊Y⌋₊ : ℕ)) : ℝ) := by
    rw [← hprod, Real.log_prod hne]
  have hle := theta34_real hY
  have h34 : (0 : ℝ) < 3.4 := by norm_num
  have hlogle : Real.log (((primorial ⌊Y⌋₊ : ℕ)) : ℝ) ≤ Y * Real.log 3.4 := by
    have h1 := Real.log_le_log hpos hle
    rwa [Real.log_rpow h34] at h1
  rw [hlog]
  exact hlogle

/-- One level layer bounded via the primorial estimate. -/
lemma U9_Bi_le (n : ℕ) (_hn : 1 ≤ n) (B : Finset ℕ)
    (hBmem : ∀ p ∈ B, p.Prime ∧ p ≤ 1890 * n)
    (i : ℕ) (hi : 1 ≤ i) (jm : ℝ) (_hjm : 1 ≤ jm)
    (hle_i : ∀ p : ℕ, p.Prime → p ≤ 1890 * n → (i : ℤ) ≤ G9r ((n : ℝ) / ((p : ℕ) : ℝ)) →
      ((p : ℕ) : ℝ) ≤ 18900 * (n : ℝ) / jm)
    (hYnn : 0 ≤ 18900 * (n : ℝ) / jm) :
    ∑ p ∈ B.filter (fun p => i ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
        Real.log ((p : ℕ) : ℝ)
      ≤ 18900 * (n : ℝ) / jm * Real.log 3.4 := by
  classical
  have hsub : B.filter (fun p => i ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat)
      ⊆ Nat.primesBelow (⌊18900 * (n : ℝ) / jm⌋₊ + 1) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpB, hiM⟩ := hp
    obtain ⟨hpp, hle⟩ := hBmem p hpB
    have hG := U9_of_toNat hi hiM
    have hple := hle_i p hpp hle hG
    have hpfloor : p ≤ ⌊18900 * (n : ℝ) / jm⌋₊ := Nat.le_floor hple
    rw [Nat.mem_primesBelow]
    exact ⟨by omega, hpp⟩
  calc ∑ p ∈ B.filter (fun p => i ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
          Real.log ((p : ℕ) : ℝ)
      ≤ ∑ p ∈ Nat.primesBelow (⌊18900 * (n : ℝ) / jm⌋₊ + 1),
          Real.log ((p : ℕ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by
          intro p hp _
          exact U9_logp_nonneg (Nat.mem_primesBelow.mp hp).2)
    _ ≤ 18900 * (n : ℝ) / jm * Real.log 3.4 := U9_theta_le _ hYnn

/-- Large-square prime contribution bounded by the `c_9` term. -/
lemma U9_B_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ ((Nat.primesBelow (2100 * n + 1)).filter (fun p => p ≤ 1890 * n)).filter
      (fun p => 2100 * n < p ^ 2),
      ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
    ≤ (18900 / 279 + 18900 / 657 + 18900 / 963 : ℝ) * (n : ℝ) * Real.log 3.4 := by
  classical
  set B := ((Nat.primesBelow (2100 * n + 1)).filter (fun p => p ≤ 1890 * n)).filter
    (fun p => 2100 * n < p ^ 2) with hBdef
  have hBmem : ∀ p ∈ B, p.Prime ∧ p ≤ 1890 * n := by
    intro p hp
    rw [hBdef, Finset.mem_filter] at hp
    obtain ⟨hpT, -⟩ := hp
    rw [Finset.mem_filter] at hpT
    obtain ⟨hpS, hle⟩ := hpT
    exact ⟨(Nat.mem_primesBelow.mp hpS).2, hle⟩
  have hsq : ∀ p ∈ B, 2100 * n < p ^ 2 := by
    intro p hp
    rw [hBdef, Finset.mem_filter] at hp
    exact hp.2
  have hsingle : ∀ p ∈ B, ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      = ((G9r ((n : ℝ) / ((p : ℕ) : ℝ)) : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
    intro p hp
    obtain ⟨hpp, -⟩ := hBmem p hp
    have hbig : 10 * Q9 * n < p ^ 2 := by rw [U9_10Q9 n]; exact hsq p hp
    rw [nu9_eq_single hpp hn hbig]
  have hMle : ∀ p ∈ B,
      ((G9r ((n : ℝ) / ((p : ℕ) : ℝ)) : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      ≤ ((((G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat : ℕ)) : ℝ)
        * Real.log ((p : ℕ) : ℝ) := by
    intro p hp
    obtain ⟨hpp, -⟩ := hBmem p hp
    exact mul_le_mul_of_nonneg_right (U9_G_toNat _) (U9_logp_nonneg hpp)
  have hM3 : ∀ p ∈ B, (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat ≤ 3 := by
    intro p hp
    apply U9_toNat_le3
    positivity
  have hLc := U9_layercake B (fun p => (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat)
    (fun p => Real.log ((p : ℕ) : ℝ)) hM3
  have hLc' : ∑ p ∈ B,
        ((((G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat : ℕ)) : ℝ)
          * Real.log ((p : ℕ) : ℝ)
      = ∑ i ∈ Finset.Icc 1 3,
        ∑ p ∈ B.filter (fun p => i ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
        Real.log ((p : ℕ) : ℝ) := hLc
  have hexpand : ∑ p ∈ B,
        ((((G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat : ℕ)) : ℝ)
          * Real.log ((p : ℕ) : ℝ)
      = (∑ p ∈ B.filter (fun p => 1 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
          Real.log ((p : ℕ) : ℝ))
        + ((∑ p ∈ B.filter (fun p => 2 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
          Real.log ((p : ℕ) : ℝ))
        + (∑ p ∈ B.filter (fun p => 3 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
          Real.log ((p : ℕ) : ℝ))) := by
    have e1 := hLc'
    rw [show Finset.Icc 1 3 = {1, 2, 3} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at e1
    exact e1
  have g1 : (∑ p ∈ B.filter (fun p => 1 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
        Real.log ((p : ℕ) : ℝ)) ≤ 18900 * (n : ℝ) / 279 * Real.log 3.4 :=
    U9_Bi_le n hn B hBmem 1 (by norm_num) 279 (by norm_num)
      (fun p hpp hle hG => U9_ple1 n p hn hpp hle (by simpa using hG)) (by positivity)
  have g2 : (∑ p ∈ B.filter (fun p => 2 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
        Real.log ((p : ℕ) : ℝ)) ≤ 18900 * (n : ℝ) / 657 * Real.log 3.4 :=
    U9_Bi_le n hn B hBmem 2 (by norm_num) 657 (by norm_num)
      (fun p hpp hle hG => U9_ple2 n p hn hpp hle (by simpa using hG)) (by positivity)
  have g3 : (∑ p ∈ B.filter (fun p => 3 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
        Real.log ((p : ℕ) : ℝ)) ≤ 18900 * (n : ℝ) / 963 * Real.log 3.4 :=
    U9_Bi_le n hn B hBmem 3 (by norm_num) 963 (by norm_num)
      (fun p hpp hle hG => U9_ple3 n p hn hpp hle (by simpa using hG)) (by positivity)
  have hcoef : (18900 * (n : ℝ) / 279 + (18900 * (n : ℝ) / 657
      + 18900 * (n : ℝ) / 963)) * Real.log 3.4
      = (18900 / 279 + 18900 / 657 + 18900 / 963 : ℝ) * (n : ℝ) * Real.log 3.4 := by
    ring
  calc ∑ p ∈ B, ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      = ∑ p ∈ B, ((G9r ((n : ℝ) / ((p : ℕ) : ℝ)) : ℤ) : ℝ)
        * Real.log ((p : ℕ) : ℝ) := Finset.sum_congr rfl hsingle
    _ ≤ ∑ p ∈ B, ((((G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat : ℕ)) : ℝ)
        * Real.log ((p : ℕ) : ℝ) := Finset.sum_le_sum hMle
    _ = (∑ p ∈ B.filter (fun p => 1 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
          Real.log ((p : ℕ) : ℝ))
        + ((∑ p ∈ B.filter (fun p => 2 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
          Real.log ((p : ℕ) : ℝ))
        + (∑ p ∈ B.filter (fun p => 3 ≤ (G9r ((n : ℝ) / ((p : ℕ) : ℝ))).toNat),
          Real.log ((p : ℕ) : ℝ))) := hexpand
    _ ≤ (18900 * (n : ℝ) / 279 + (18900 * (n : ℝ) / 657
        + 18900 * (n : ℝ) / 963)) * Real.log 3.4 := by
        have hle := add_le_add (add_le_add g1 g2) g3
        linarith [hle]
    _ = (18900 / 279 + 18900 / 657 + 18900 / 963 : ℝ) * (n : ℝ) * Real.log 3.4 :=
        hcoef

/-- One small-square prime term bounded by `3 * log (2100 * n)`. -/
lemma U9_Cterm_le (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime)
    (_hleX : p ^ 2 ≤ 2100 * n) :
    ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      ≤ 3 * Real.log (((2100 * n : ℕ)) : ℝ) := by
  have hXpos : 0 < 2100 * n := by omega
  have hXne : (2100 * n : ℕ) ≠ 0 := ne_of_gt hXpos
  have hnu : nu9 p n
      = ∑ j ∈ Finset.Ico 1 (Nat.log p (10 * Q9 * n) + 2),
        G9r ((n : ℝ) / ((((p ^ j : ℕ))) : ℝ)) := nu9_eq_sum_G hp (by omega)
  have hvan : ∀ j ∈ Finset.Ico 1 (Nat.log p (10 * Q9 * n) + 2),
      j ∉ Finset.Icc 1 (Nat.log p (2100 * n)) →
      G9r ((n : ℝ) / ((((p ^ j : ℕ))) : ℝ)) = 0 := by
    intro j hjIco hjIcc
    rw [Finset.mem_Ico] at hjIco
    rw [Finset.mem_Icc] at hjIcc
    have hLt : Nat.log p (2100 * n) < j := by
      by_contra hc
      push Not at hc
      exact hjIcc ⟨hjIco.1, hc⟩
    have hle : ¬ p ^ j ≤ 2100 * n := by
      intro hlej
      have hlj := Nat.le_log_of_pow_le hp.one_lt hlej
      omega
    have hlt : 2100 * n < p ^ j := lt_of_not_ge hle
    have h10 : 10 * Q9 * n < p ^ j := by rw [U9_10Q9 n]; exact hlt
    exact G9r_vanish_of hp hn h10
  have hsub : Finset.Icc 1 (Nat.log p (2100 * n))
      ⊆ Finset.Ico 1 (Nat.log p (10 * Q9 * n) + 2) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_Ico]
    have hlog_eq : Nat.log p (10 * Q9 * n) = Nat.log p (2100 * n) := by
      rw [U9_10Q9 n]
    omega
  have hsplit : (∑ j ∈ Finset.Ico 1 (Nat.log p (10 * Q9 * n) + 2),
        G9r ((n : ℝ) / ((((p ^ j : ℕ))) : ℝ)))
      = ∑ j ∈ Finset.Icc 1 (Nat.log p (2100 * n)),
        G9r ((n : ℝ) / ((((p ^ j : ℕ))) : ℝ)) :=
    (Finset.sum_subset hsub (fun j hjIco hjNIcc => hvan j hjIco hjNIcc)).symm
  have hbd : (∑ j ∈ Finset.Icc 1 (Nat.log p (2100 * n)),
        G9r ((n : ℝ) / ((((p ^ j : ℕ))) : ℝ)))
      ≤ (Nat.log p (2100 * n) : ℤ) * 3 := by
    calc _ ≤ ∑ _j ∈ Finset.Icc 1 (Nat.log p (2100 * n)), (3 : ℤ) :=
          Finset.sum_le_sum (fun j _ => G9r_le3 _ (by positivity))
      _ = (Nat.log p (2100 * n) : ℤ) * 3 := by
          have hc : (Finset.Icc 1 (Nat.log p (2100 * n))).card
              = Nat.log p (2100 * n) := by
            rw [Nat.card_Icc]
            omega
          rw [Finset.sum_const, nsmul_eq_mul, hc]
  have hnu_le : (nu9 p n : ℤ) ≤ (Nat.log p (2100 * n) : ℤ) * 3 := by
    rw [hnu, hsplit]
    exact hbd
  have hpow : p ^ Nat.log p (2100 * n) ≤ 2100 * n :=
    Nat.pow_log_le_self p hXne
  have hpowR : ((((p : ℕ)) : ℝ) ^ Nat.log p (2100 * n))
      ≤ (((2100 * n : ℕ)) : ℝ) := by
    exact_mod_cast hpow
  have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.pos
  have hlogLp : ((Nat.log p (2100 * n) : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      ≤ Real.log (((2100 * n : ℕ)) : ℝ) := by
    have h1 : Real.log ((((p : ℕ)) : ℝ) ^ Nat.log p (2100 * n))
        ≤ Real.log (((2100 * n : ℕ)) : ℝ) :=
      Real.log_le_log (pow_pos hpR _) hpowR
    rwa [Real.log_pow] at h1
  have hnuR : ((nu9 p n : ℤ) : ℝ)
      ≤ ((Nat.log p (2100 * n) : ℕ) : ℝ) * 3 := by
    exact_mod_cast hnu_le
  have hlogp := U9_logp_nonneg hp
  calc ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      ≤ ((((Nat.log p (2100 * n) : ℕ) : ℝ)) * 3) * Real.log ((p : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hnuR hlogp
    _ = 3 * ((((Nat.log p (2100 * n) : ℕ) : ℝ)) * Real.log ((p : ℕ) : ℝ)) := by
        ring
    _ ≤ 3 * Real.log (((2100 * n : ℕ)) : ℝ) :=
        mul_le_mul_of_nonneg_left hlogLp (by norm_num)

/-- Few small-square primes: count bounded by `√(2100 * n) / 3`. -/
lemma U9_Ccard_le (n : ℕ) (hn : 1 ≤ n) (C : Finset ℕ)
    (hC : ∀ p ∈ C, p.Prime ∧ p ^ 2 ≤ 2100 * n) :
    (C.card : ℝ) ≤ Real.sqrt (((2100 * n : ℕ)) : ℝ) / 3 := by
  have hXnn : (0 : ℝ) ≤ (((2100 * n : ℕ)) : ℝ) := Nat.cast_nonneg _
  have hsub : C ⊆ Nat.primesBelow (⌊Real.sqrt (((2100 * n : ℕ)) : ℝ)⌋₊ + 1) := by
    intro p hp
    obtain ⟨hpp, hsq⟩ := hC p hp
    have hpsq : (((p : ℕ)) : ℝ) ^ 2 ≤ (((2100 * n : ℕ)) : ℝ) := by
      exact_mod_cast hsq
    have hpRnn : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
    have hple : ((p : ℕ) : ℝ) ≤ Real.sqrt (((2100 * n : ℕ)) : ℝ) :=
      (Real.le_sqrt hpRnn hXnn).mpr hpsq
    have hpfloor : p ≤ ⌊Real.sqrt (((2100 * n : ℕ)) : ℝ)⌋₊ := Nat.le_floor hple
    rw [Nat.mem_primesBelow]
    exact ⟨by omega, hpp⟩
  have hcard : C.card ≤ Nat.primeCounting ⌊Real.sqrt (((2100 * n : ℕ)) : ℝ)⌋₊ := by
    have h1 := Finset.card_le_card hsub
    rw [Nat.primesBelow_card_eq_primeCounting'] at h1
    exact h1
  have hXge : (2100 : ℝ) ≤ (((2100 * n : ℕ)) : ℝ) := by
    have h1 : 2100 ≤ 2100 * n := by
      calc (2100 : ℕ) = 2100 * 1 := by ring
        _ ≤ 2100 * n := by gcongr
    exact_mod_cast h1
  have h36 : (36 : ℝ) ≤ Real.sqrt (((2100 * n : ℕ)) : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hXnn]
    have h36sq : (36 : ℝ) ^ 2 = 1296 := by norm_num
    rw [h36sq]
    linarith [hXge]
  have hpi := pi_third h36
  have hcardR : (C.card : ℝ)
      ≤ (Nat.primeCounting ⌊Real.sqrt (((2100 * n : ℕ)) : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast hcard
  linarith [hcardR, hpi]

/-- Small-square prime contribution bounded by the square-root term. -/
lemma U9_C_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ ((Nat.primesBelow (2100 * n + 1)).filter (fun p => p ≤ 1890 * n)).filter
      (fun p => ¬ 2100 * n < p ^ 2),
      ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
    ≤ Real.sqrt (2100 * (n : ℝ)) * Real.log (2100 * (n : ℝ)) := by
  classical
  set C := ((Nat.primesBelow (2100 * n + 1)).filter (fun p => p ≤ 1890 * n)).filter
    (fun p => ¬ 2100 * n < p ^ 2) with hCdef
  have hCmem : ∀ p ∈ C, p.Prime ∧ p ^ 2 ≤ 2100 * n := by
    intro p hp
    rw [hCdef, Finset.mem_filter] at hp
    obtain ⟨hpT, hnc⟩ := hp
    rw [Finset.mem_filter] at hpT
    obtain ⟨hpS, -⟩ := hpT
    exact ⟨(Nat.mem_primesBelow.mp hpS).2, Nat.not_lt.mp hnc⟩
  have hX1 : (1 : ℝ) ≤ (((2100 * n : ℕ)) : ℝ) := by
    have h1 : 1 ≤ 2100 * n := by omega
    exact_mod_cast h1
  have hterm : ∀ p ∈ C, ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      ≤ 3 * Real.log (((2100 * n : ℕ)) : ℝ) := by
    intro p hp
    obtain ⟨hpp, hsq⟩ := hCmem p hp
    exact U9_Cterm_le n p hn hpp hsq
  have hcard := U9_Ccard_le n hn C hCmem
  have hlogXnn : 0 ≤ Real.log (((2100 * n : ℕ)) : ℝ) := Real.log_nonneg hX1
  have hXeq : (((2100 * n : ℕ)) : ℝ) = 2100 * (n : ℝ) := by simp
  calc ∑ p ∈ C, ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      ≤ ∑ _p ∈ C, 3 * Real.log (((2100 * n : ℕ)) : ℝ) := Finset.sum_le_sum hterm
    _ = (C.card : ℝ) * (3 * Real.log (((2100 * n : ℕ)) : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Real.sqrt (((2100 * n : ℕ)) : ℝ) / 3)
        * (3 * Real.log (((2100 * n : ℕ)) : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard (by linarith [hlogXnn])
    _ = Real.sqrt (2100 * (n : ℝ)) * Real.log (2100 * (n : ℝ)) := by
        rw [hXeq]
        ring

/-- Upper bound for `logF9 n` assuming no prime in `(1890 * n, 2100 * n]`. -/
theorem logF9_upper (n : ℕ) (hn : 1 ≤ n)
    (hA : ∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False) :
    logF9 n ≤ (18900 / 279 + 18900 / 657 + 18900 / 963 : ℝ) * n * Real.log 3.4
      + Real.sqrt (2100 * n) * Real.log (2100 * n) := by
  classical
  rw [U9_bridge n hn]
  have hST : Nat.primesBelow (2100 * n + 1)
      = (Nat.primesBelow (2100 * n + 1)).filter (fun p => p ≤ 1890 * n) := by
    symm
    apply Finset.filter_true_of_mem
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    by_contra hc
    push Not at hc
    exact hA p hp.2 hc (by omega)
  rw [hST]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Nat.primesBelow (2100 * n + 1)).filter (fun p => p ≤ 1890 * n))
    (fun p => 2100 * n < p ^ 2)
    (fun p => ((nu9 p n : ℤ) : ℝ) * Real.log ((p : ℕ) : ℝ))
  have hB := U9_B_le n hn
  have hC := U9_C_le n hn
  rw [← hsplit]
  exact add_le_add hB hC

end MathlibExt.NumberTheory.BreuschWanted.Internal
