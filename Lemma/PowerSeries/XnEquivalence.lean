import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.RingTheory.PowerSeries.XnEquivalence
open PowerSeries
open scoped PowerSeries BigOperators Polynomial


section
-- ac-theorems

open Polynomial Finset

namespace PowerSeries

variable {R : Type*} [CommSemiring R]


/-- x^n-equivalence is reflexive. -/
lemma XnEquiv.refl (n : ℕ) (f : R⟦X⟧) : XnEquiv n f f :=
  fun _ _ => rfl

/-- x^n-equivalence is symmetric. -/
lemma XnEquiv.symm {n : ℕ} {f g : R⟦X⟧} (h : XnEquiv n f g) : XnEquiv n g f :=
  fun m hm => (h m hm).symm

/-- x^n-equivalence is transitive. -/
lemma XnEquiv.trans {n : ℕ} {f g h : R⟦X⟧} (hfg : XnEquiv n f g) (hgh : XnEquiv n g h) :
    XnEquiv n f h :=
  fun m hm => (hfg m hm).trans (hgh m hm)

/-- x^n-equivalence is an equivalence relation (Theorem `thm.fps.xneq.props` (a)). -/
lemma XnEquiv.equivalence (n : ℕ) : Equivalence (XnEquiv n : R⟦X⟧ → R⟦X⟧ → Prop) :=
  ⟨XnEquiv.refl n, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- x^n-equivalence implies x^m-equivalence for m ≤ n. -/
lemma XnEquiv.of_le {m n : ℕ} (hmn : m ≤ n) {f g : R⟦X⟧} (h : XnEquiv n f g) : XnEquiv m f g :=
  fun k hk => h k (hk.trans hmn)


/-- x^0-equivalence is equivalent to having equal constant coefficients.
This is a useful simplification lemma for the base case of x^n-equivalence. -/
@[simp]
lemma XnEquiv_zero_iff (f g : R⟦X⟧) :
    XnEquiv 0 f g ↔ constantCoeff f = constantCoeff g := by
  constructor
  · intro h
    have := h 0 (Nat.zero_le 0)
    simp only [coeff_zero_eq_constantCoeff_apply] at this
    exact this
  · intro h m hm
    simp only [Nat.le_zero] at hm
    rw [hm]
    simp only [coeff_zero_eq_constantCoeff_apply]
    exact h

/-- Any FPS is x^n-equivalent to itself (reflexivity as a simp lemma). -/
@[simp]
lemma XnEquiv_self (n : ℕ) (f : R⟦X⟧) : XnEquiv n f f := XnEquiv.refl n f


/-- x^n-equivalence is preserved by addition (Theorem `thm.fps.xneq.props` (b), eq.thm.fps.xneq.props.b.+). -/
lemma XnEquiv.add {n : ℕ} {a b c d : R⟦X⟧} (hab : XnEquiv n a b) (hcd : XnEquiv n c d) :
    XnEquiv n (a + c) (b + d) := fun m hm => by
  simp only [map_add]
  rw [hab m hm, hcd m hm]

/-- x^n-equivalence is preserved by subtraction (Theorem `thm.fps.xneq.props` (b), eq.thm.fps.xneq.props.b.-). -/
lemma XnEquiv.sub {R : Type*} [CommRing R] {n : ℕ} {a b c d : R⟦X⟧}
    (hab : XnEquiv n a b) (hcd : XnEquiv n c d) : XnEquiv n (a - c) (b - d) := fun m hm => by
  simp only [map_sub]
  rw [hab m hm, hcd m hm]

/-- x^n-equivalence is preserved by scalar multiplication (Theorem `thm.fps.xneq.props` (c)). -/
lemma XnEquiv.smul {n : ℕ} {a b : R⟦X⟧} (hab : XnEquiv n a b) (r : R) :
    XnEquiv n (r • a) (r • b) := fun m hm => by
  simp only [coeff_smul, hab m hm]

/-- x^n-equivalence is preserved by multiplication (Theorem `thm.fps.xneq.props` (b), eq.thm.fps.xneq.props.b.*). -/
lemma XnEquiv.mul {n : ℕ} {a b c d : R⟦X⟧} (hab : XnEquiv n a b) (hcd : XnEquiv n c d) :
    XnEquiv n (a * c) (b * d) := fun m hm => by
  simp only [coeff_mul]
  apply Finset.sum_congr rfl
  intro ⟨i, j⟩ hij
  simp only [HasAntidiagonal.mem_antidiagonal] at hij
  have hi : i ≤ n := by omega
  have hj : j ≤ n := by omega
  rw [hab i hi, hcd j hj]


/-- x^n-equivalence is preserved by negation. -/
lemma XnEquiv.neg {R : Type*} [CommRing R] {n : ℕ} {a b : R⟦X⟧}
    (hab : XnEquiv n a b) : XnEquiv n (-a) (-b) := fun m hm => by
  simp only [map_neg, hab m hm]

/-- x^n-equivalence is preserved by inversion via `invOfUnit` for FPS with invertible constant term
(Theorem `thm.fps.xneq.props` (d)).

The proof proceeds by strong induction on the coefficient index, using the formula
for coefficients of the inverse. -/
lemma XnEquiv.invOfUnit {R : Type*} [CommRing R] {n : ℕ} {a b : R⟦X⟧}
    (ua : Rˣ) (ub : Rˣ) (ha : constantCoeff a = ua) (hb : constantCoeff b = ub)
    (hab : XnEquiv n a b) : XnEquiv n (invOfUnit a ua) (invOfUnit b ub) := by
  -- First, show that ua = ub since constant coefficients agree
  have huab : (ua : R) = (ub : R) := by
    have h0 := hab 0 (Nat.zero_le n)
    simp only [coeff_zero_eq_constantCoeff_apply] at h0
    rw [ha, hb] at h0
    exact h0
  have huab_inv : (ua⁻¹ : Rˣ) = (ub⁻¹ : Rˣ) := by
    congr 1
    exact Units.ext huab
  -- Now prove by strong induction on the coefficient index
  intro m hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [coeff_invOfUnit, coeff_invOfUnit]
    split_ifs with hm0
    · -- Case m = 0: both sides are u⁻¹
      simp only [huab_inv]
    · -- Case m > 0: need to show the sums are equal
      congr 1
      · simp only [huab_inv]
      · apply Finset.sum_congr rfl
        intro ⟨i, j⟩ hij
        simp only [HasAntidiagonal.mem_antidiagonal] at hij
        split_ifs with hj
        · -- When j < m, we can use induction hypothesis
          have hi : i ≤ n := by omega
          have hj' : j ≤ n := by omega
          rw [hab i hi, ih j hj hj']
        · rfl

/-- x^n-equivalence is preserved by inversion for FPS over a field
(Theorem `thm.fps.xneq.props` (d)). -/
lemma XnEquiv.inv {K : Type*} [Field K] {n : ℕ} {a b : K⟦X⟧}
    (ha : constantCoeff a ≠ 0) (hb : constantCoeff b ≠ 0)
    (hab : XnEquiv n a b) : XnEquiv n a⁻¹ b⁻¹ := by
  -- Use Units.mk0 to create units from the non-zero constant coefficients
  let ua : Kˣ := Units.mk0 (constantCoeff a) ha
  let ub : Kˣ := Units.mk0 (constantCoeff b) hb
  -- Rewrite inverses as invOfUnit
  rw [← invOfUnit_eq a ha, ← invOfUnit_eq b hb]
  -- Apply the invOfUnit theorem
  exact XnEquiv.invOfUnit ua ub rfl rfl hab

/-- Variant of `XnEquiv.invOfUnit` where the units may be different but their values agree.
This is useful when working with limits where we have different units for each term. -/
lemma XnEquiv.invOfUnit' {R : Type*} [CommRing R] {n : ℕ} {f g : R⟦X⟧} (u v : Rˣ)
    (huv : (u : R) = (v : R))
    (hfg : XnEquiv n f g) : XnEquiv n (PowerSeries.invOfUnit f u) (PowerSeries.invOfUnit g v) := by
  have huv_inv : (u⁻¹ : Rˣ) = (v⁻¹ : Rˣ) := by
    congr 1
    exact Units.ext huv
  intro m hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [coeff_invOfUnit, coeff_invOfUnit]
    split_ifs with hm0
    · simp only [huv_inv]
    · congr 1
      · simp only [huv_inv]
      · apply Finset.sum_congr rfl
        intro ⟨i, j⟩ hij
        simp only [HasAntidiagonal.mem_antidiagonal] at hij
        split_ifs with hj
        · have hi : i ≤ n := by omega
          have hj' : j ≤ n := by omega
          rw [hfg i hi, ih j hj hj']
        · rfl

/-- x^n-equivalence is preserved by division (Theorem `thm.fps.xneq.props` (e)). -/
lemma XnEquiv.div {R : Type*} [CommRing R] {n : ℕ} {a b c d : R⟦X⟧}
    (hab : XnEquiv n a b) (hcd : XnEquiv n c d)
    (u : Rˣ) (hu : constantCoeff c = u)
    (v : Rˣ) (hv : constantCoeff d = v) :
    XnEquiv n (a * PowerSeries.invOfUnit c u) (b * PowerSeries.invOfUnit d v) := by
  have huv : (u : R) = (v : R) := by
    have h0 := hcd 0 (Nat.zero_le n)
    simp only [coeff_zero_eq_constantCoeff_apply] at h0
    rw [hu, hv] at h0
    exact h0
  apply XnEquiv.mul hab
  exact XnEquiv.invOfUnit' u v huv hcd


variable {ι : Type*}

/-- x^n-equivalence is preserved by finite sums (Theorem `thm.fps.xneq.props` (f), eq.thm.fps.xneq.props.e.+). -/
lemma XnEquiv.sum [DecidableEq ι] {n : ℕ} {s : Finset ι} {a b : ι → R⟦X⟧}
    (h : ∀ i ∈ s, XnEquiv n (a i) (b i)) : XnEquiv n (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    exact XnEquiv.refl n 0
  | @insert x s hxs ih =>
    rw [sum_insert hxs, sum_insert hxs]
    apply XnEquiv.add
    · exact h x (mem_insert_self x s)
    · exact ih (fun i hi' => h i (mem_insert_of_mem hi'))

/-- x^n-equivalence is preserved by finite products (Theorem `thm.fps.xneq.props` (f), eq.thm.fps.xneq.props.e.*). -/
lemma XnEquiv.prod [DecidableEq ι] {n : ℕ} {s : Finset ι} {a b : ι → R⟦X⟧}
    (h : ∀ i ∈ s, XnEquiv n (a i) (b i)) : XnEquiv n (∏ i ∈ s, a i) (∏ i ∈ s, b i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty]
    exact XnEquiv.refl n 1
  | @insert x s hxs ih =>
    rw [prod_insert hxs, prod_insert hxs]
    apply XnEquiv.mul
    · exact h x (mem_insert_self x s)
    · exact ih (fun i hi' => h i (mem_insert_of_mem hi'))


/-- x^n-equivalence is equivalent to divisibility by X^(n+1)
(Proposition `prop.fps.xneq-multiple`).

Two FPS f and g satisfy f ≡ g [mod X^(n+1)] if and only if X^(n+1) divides f - g.

This is the main characterization theorem that connects the coefficient-wise
definition of x^n-equivalence to the divisibility formulation. -/
lemma xnEquiv_iff_dvd {R : Type*} [CommRing R] {n : ℕ} {f g : R⟦X⟧} :
    XnEquiv n f g ↔ (X : R⟦X⟧) ^ (n + 1) ∣ f - g := by
  rw [PowerSeries.X_pow_dvd_iff]
  constructor
  · intro h m hm
    simp only [map_sub]
    have hm' : m ≤ n := Nat.lt_succ_iff.mp hm
    rw [h m hm']
    ring
  · intro h m hm
    have hm' : m < n + 1 := Nat.lt_succ_of_le hm
    specialize h m hm'
    simp only [map_sub] at h
    exact sub_eq_zero.mp h

/-- Alternative statement of `prop.fps.xneq-multiple`:
f ≡ g [mod X^(n+1)] iff f - g is a multiple of X^(n+1).

This is definitionally equal to `xnEquiv_iff_dvd` since divisibility is defined
as the existence of such a quotient. The explicit existential form is sometimes
more convenient to work with. -/
lemma xnEquiv_iff_sub_eq_mul_X_pow {R : Type*} [CommRing R] {n : ℕ} {f g : R⟦X⟧} :
    XnEquiv n f g ↔ ∃ q : R⟦X⟧, f - g = X ^ (n + 1) * q := by
  rw [xnEquiv_iff_dvd]; rfl


/-- x^n-equivalence is equivalent to having equal truncations. -/
lemma xnEquiv_iff_trunc {n : ℕ} {f g : R⟦X⟧} :
    XnEquiv n f g ↔ trunc (n + 1) f = trunc (n + 1) g := by
  constructor
  · intro h
    ext m
    simp only [coeff_trunc]
    split_ifs with hm
    · exact h m (Nat.lt_succ_iff.mp hm)
    · rfl
  · intro h m hm
    have hm' : m < n + 1 := Nat.lt_succ_of_le hm
    have : (trunc (n + 1) f).coeff m = (trunc (n + 1) g).coeff m := by rw [h]
    simp only [coeff_trunc, hm', ↓reduceIte] at this
    exact this

/-- Every FPS is x^n-equivalent to some polynomial (Example (d) in the source). -/
lemma exists_polynomial_xnEquiv (n : ℕ) (f : R⟦X⟧) :
    ∃ p : R[X], XnEquiv n f p := by
  use trunc (n + 1) f
  intro m hm
  rw [Polynomial.coeff_coe, coeff_trunc]
  simp only [Nat.lt_succ_of_le hm, ↓reduceIte]


/-- x^n-equivalence is preserved by powers. -/
lemma XnEquiv.pow {n : ℕ} {a b : R⟦X⟧} (hab : XnEquiv n a b) (k : ℕ) :
    XnEquiv n (a ^ k) (b ^ k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    exact XnEquiv.refl n 1
  | succ k ih =>
    simp only [pow_succ]
    exact ih.mul hab


/-- Coefficients of f^k are zero for indices < k when constantCoeff f = 0.
This is a key lemma for proving that composition preserves x^n-equivalence. -/
lemma coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero {R : Type*} [CommRing R]
    {f : R⟦X⟧} (hf : constantCoeff f = 0) {m k : ℕ} (hmk : m < k) : coeff m (f ^ k) = 0 := by
  apply coeff_of_lt_order
  calc (m : ℕ∞) < k := by exact_mod_cast hmk
    _ ≤ (f ^ k).order := le_order_pow_of_constantCoeff_eq_zero k hf

/-- x^n-equivalence is preserved by composition when the inner series have constant term 0
(Proposition `prop.fps.xneq.comp`).

If a ≡ b [mod X^(n+1)] and c ≡ d [mod X^(n+1)] with [x^0]c = 0 and [x^0]d = 0,
then a ∘ c ≡ b ∘ d [mod X^(n+1)].

The proof follows the sketch in the source text:
1. Write a = ∑ aᵢ xⁱ and b = ∑ bᵢ xⁱ
2. For i ≤ n: aᵢ = bᵢ (by hab) and c^i ≡ d^i [mod X^(n+1)] (by XnEquiv.pow)
3. For i > n: [x^m](c^i) = [x^m](d^i) = 0 for all m ≤ n (since constantCoeff = 0)
4. Therefore a ∘ c ≡ b ∘ d [mod X^(n+1)] -/
lemma XnEquiv.comp {R : Type*} [CommRing R] {n : ℕ} {a b c d : R⟦X⟧}
    (hab : XnEquiv n a b) (hcd : XnEquiv n c d)
    (hc : constantCoeff c = 0) (hd : constantCoeff d = 0) :
    XnEquiv n (a.subst c) (b.subst d) := by
  intro m hm
  -- Use the coefficient formula for substitution
  have hc_subst : HasSubst c := HasSubst.of_constantCoeff_zero' hc
  have hd_subst : HasSubst d := HasSubst.of_constantCoeff_zero' hd
  rw [coeff_subst' hc_subst, coeff_subst' hd_subst]
  -- Show that each term in the finsum is equal
  have term_eq : ∀ k, coeff k a • coeff m (c ^ k) = coeff k b • coeff m (d ^ k) := by
    intro k
    by_cases hk : k ≤ n
    · -- For k ≤ n, use hab and XnEquiv.pow hcd
      have h1 : coeff k a = coeff k b := hab k hk
      have h2 : coeff m (c ^ k) = coeff m (d ^ k) := (hcd.pow k) m hm
      rw [h1, h2]
    · -- For k > n, both coefficients of c^k and d^k at m are 0
      push Not at hk
      have hm_lt_k : m < k := Nat.lt_of_le_of_lt hm hk
      have h1 : coeff m (c ^ k) = 0 :=
        coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero hc hm_lt_k
      have h2 : coeff m (d ^ k) = 0 :=
        coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero hd hm_lt_k
      rw [h1, h2, smul_zero, smul_zero]
  -- The finsums are equal because all terms are equal
  congr 1
  ext k
  exact term_eq k


/-- Two FPS are equal iff they are x^n-equivalent for all n. -/
lemma eq_iff_forall_xnEquiv {f g : R⟦X⟧} : f = g ↔ ∀ n, XnEquiv n f g := by
  constructor
  · intro h n
    rw [h]
    exact XnEquiv.refl n g
  · intro h
    ext m
    exact h m m le_rfl

end PowerSeries

end


/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_refl_is
-- given
  {R : Type*} [CommSemiring R] (n : ℕ) (f : R⟦X⟧) :
-- imply
  XnEquiv n f f := by
-- proof
  apply PowerSeries.XnEquiv.refl n f

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_symm_is
-- given
  {R : Type*} [CommSemiring R] {n : ℕ} {f g : R⟦X⟧}
  (h : XnEquiv n f g) :
-- imply
  XnEquiv n g f := by
-- proof
  apply PowerSeries.XnEquiv.symm h

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_trans_is
-- given
  {R : Type*} [CommSemiring R] {n : ℕ} {f g h : R⟦X⟧}
  (hfg : XnEquiv n f g) (hgh : XnEquiv n g h) :
-- imply
  XnEquiv n f h := by
-- proof
  apply PowerSeries.XnEquiv.trans hfg hgh

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_equivalence_is
-- given
  {R : Type*} [CommSemiring R] (n : ℕ) :
-- imply
  Equivalence (XnEquiv n : R⟦X⟧ → R⟦X⟧ → Prop) := by
-- proof
  apply PowerSeries.XnEquiv.equivalence n

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_of_le_is
-- given
  {R : Type*} [CommSemiring R] {m n : ℕ} (hmn : m ≤ n) {f g : R⟦X⟧}
  (h : XnEquiv n f g) :
-- imply
  XnEquiv m f g := by
-- proof
  apply PowerSeries.XnEquiv.of_le hmn h

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_zero_iff
-- given
  {R : Type*} [CommSemiring R] (f g : R⟦X⟧) :
-- imply
  XnEquiv 0 f g ↔ constantCoeff f = constantCoeff g := by
-- proof
  apply PowerSeries.XnEquiv_zero_iff f g

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_self_is
-- given
  {R : Type*} [CommSemiring R] (n : ℕ) (f : R⟦X⟧) :
-- imply
  XnEquiv n f f := by
-- proof
  apply PowerSeries.XnEquiv_self n f

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_add_is
-- given
  {R : Type*} [CommSemiring R] {n : ℕ} {a b c d : R⟦X⟧}
  (hab : XnEquiv n a b) (hcd : XnEquiv n c d) :
-- imply
  XnEquiv n (a + c) (b + d) := by
-- proof
  apply PowerSeries.XnEquiv.add hab hcd

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_sub_is
-- given
  {R : Type*} [CommRing R] {n : ℕ} {a b c d : R⟦X⟧}
  (hab : XnEquiv n a b) (hcd : XnEquiv n c d) :
-- imply
  XnEquiv n (a - c) (b - d) := by
-- proof
  apply PowerSeries.XnEquiv.sub hab hcd

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_smul_is
-- given
  {R : Type*} [CommSemiring R] {n : ℕ} {a b : R⟦X⟧}
  (hab : XnEquiv n a b) (r : R) :
-- imply
  XnEquiv n (r • a) (r • b) := by
-- proof
  apply PowerSeries.XnEquiv.smul hab r

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_mul_is
-- given
  {R : Type*} [CommSemiring R] {n : ℕ} {a b c d : R⟦X⟧}
  (hab : XnEquiv n a b) (hcd : XnEquiv n c d) :
-- imply
  XnEquiv n (a * c) (b * d) := by
-- proof
  apply PowerSeries.XnEquiv.mul hab hcd

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_neg_is
-- given
  {R : Type*} [CommRing R] {n : ℕ} {a b : R⟦X⟧}
  (hab : XnEquiv n a b) :
-- imply
  XnEquiv n (-a) (-b) := by
-- proof
  apply PowerSeries.XnEquiv.neg hab

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_inv_of_unit_is
-- given
  {R : Type*} [CommRing R] {n : ℕ} {a b : R⟦X⟧}
  (ua ub : Rˣ) (ha : constantCoeff a = ua) (hb : constantCoeff b = ub)
  (hab : XnEquiv n a b) :
-- imply
  XnEquiv n (invOfUnit a ua) (invOfUnit b ub) := by
-- proof
  apply PowerSeries.XnEquiv.invOfUnit ua ub ha hb hab

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_inv_is
-- given
  {K : Type*} [Field K] {n : ℕ} {a b : K⟦X⟧}
  (ha : constantCoeff a ≠ 0) (hb : constantCoeff b ≠ 0)
  (hab : XnEquiv n a b) :
-- imply
  XnEquiv n a⁻¹ b⁻¹ := by
-- proof
  apply PowerSeries.XnEquiv.inv ha hb hab

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_inv_of_unit'_is
-- given
  {R : Type*} [CommRing R] {n : ℕ} {f g : R⟦X⟧} (u v : Rˣ)
  (huv : (u : R) = (v : R))
  (hfg : XnEquiv n f g) :
-- imply
  XnEquiv n (invOfUnit f u) (invOfUnit g v) := by
-- proof
  apply PowerSeries.XnEquiv.invOfUnit' u v huv hfg

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_div_is
-- given
  {R : Type*} [CommRing R] {n : ℕ} {a b c d : R⟦X⟧}
  (u v : Rˣ)
  (hab : XnEquiv n a b) (hcd : XnEquiv n c d)
  (hu : constantCoeff c = u) (hv : constantCoeff d = v) :
-- imply
  XnEquiv n (a * invOfUnit c u) (b * invOfUnit d v) := by
-- proof
  apply PowerSeries.XnEquiv.div hab hcd u hu v hv

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_sum_is
-- given
  {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι] {n : ℕ} {s : Finset ι}
  {a b : ι → R⟦X⟧}
  (h : ∀ i ∈ s, XnEquiv n (a i) (b i)) :
-- imply
  XnEquiv n (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
-- proof
  apply PowerSeries.XnEquiv.sum h

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_prod_is
-- given
  {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι] {n : ℕ} {s : Finset ι}
  {a b : ι → R⟦X⟧}
  (h : ∀ i ∈ s, XnEquiv n (a i) (b i)) :
-- imply
  XnEquiv n (∏ i ∈ s, a i) (∏ i ∈ s, b i) := by
-- proof
  apply PowerSeries.XnEquiv.prod h

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_dvd_iff
-- given
  {R : Type*} [CommRing R] {n : ℕ} {f g : R⟦X⟧} :
-- imply
  XnEquiv n f g ↔ (X : R⟦X⟧) ^ (n + 1) ∣ f - g := by
-- proof
  apply PowerSeries.xnEquiv_iff_dvd

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_sub_eq_mul_x_pow_iff
-- given
  {R : Type*} [CommRing R] {n : ℕ} {f g : R⟦X⟧} :
-- imply
  XnEquiv n f g ↔ ∃ q : R⟦X⟧, f - g = X ^ (n + 1) * q := by
-- proof
  apply PowerSeries.xnEquiv_iff_sub_eq_mul_X_pow

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_trunc_iff
-- given
  {R : Type*} [CommSemiring R] {n : ℕ} {f g : R⟦X⟧} :
-- imply
  XnEquiv n f g ↔ trunc (n + 1) f = trunc (n + 1) g := by
-- proof
  apply PowerSeries.xnEquiv_iff_trunc

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma exists_polynomial_xn_equiv_is
-- given
  {R : Type*} [CommSemiring R] (n : ℕ) (f : R⟦X⟧) :
-- imply
  ∃ p : R[X], XnEquiv n f p := by
-- proof
  apply PowerSeries.exists_polynomial_xnEquiv n f

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_pow_is
-- given
  {R : Type*} [CommSemiring R] {n : ℕ} {a b : R⟦X⟧}
  (hab : XnEquiv n a b) (k : ℕ) :
-- imply
  XnEquiv n (a ^ k) (b ^ k) := by
-- proof
  apply PowerSeries.XnEquiv.pow hab k

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma xn_equiv_comp_is
-- given
  {R : Type*} [CommRing R] {n : ℕ} {a b c d : R⟦X⟧}
  (hab : XnEquiv n a b) (hcd : XnEquiv n c d)
  (hc : constantCoeff c = 0) (hd : constantCoeff d = 0) :
-- imply
  XnEquiv n (a.subst c) (b.subst d) := by
-- proof
  apply PowerSeries.XnEquiv.comp hab hcd hc hd

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma eq_iff_forall_xn_equiv_iff
-- given
  {R : Type*} [CommSemiring R] {f g : R⟦X⟧} :
-- imply
  f = g ↔ ∀ n, XnEquiv n f g := by
-- proof
  apply PowerSeries.eq_iff_forall_xnEquiv

/--
[XnEquivalence](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/XnEquivalence.lean)
-/
@[path]
private lemma x_coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero
  [CommRing R]
  {f : R⟦X⟧}
  {m k : ℕ}
-- given
  (hf : constantCoeff f = 0)
  (hmk : m < k) :
-- imply
  coeff m (f ^ k) = 0 := by
-- proof
  apply PowerSeries.coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero hf hmk


-- created on 2026-10-11
-- updated on 2026-10-26
