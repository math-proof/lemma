import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.RingTheory.PowerSeries.FPSDefinition.Part3
import Lemma.PowerSeries.InfiniteProducts2


section
-- ac-theorems


open scoped Polynomial
open PowerSeries Finset Finset.HasAntidiagonal Finset.Nat

namespace AlgebraicCombinatorics

namespace FPS

variable {R : Type*} [CommRing R]

/-- The FPS (a₀, a₁, a₂, ...) is constructed from a sequence using `PowerSeries.mk`.
    This is the inverse of coefficient extraction. -/
lemma fps_mk_eq_symm (a : ℕ → R) : PowerSeries.mk a = fpsEquivSeq.symm a := rfl

/-- Extracting coefficients from an FPS gives back the original sequence
    (Definition def.fps.fps). -/
lemma fps_coeff_mk (a : ℕ → R) (n : ℕ) : coeff n (PowerSeries.mk a) = a n := coeff_mk n a

/-- Any FPS equals the FPS constructed from its coefficient sequence
    (Definition def.fps.fps). This shows that every FPS is determined by its coefficients. -/
lemma fps_eq_mk_coeff (f : R⟦X⟧) : f = PowerSeries.mk (fun n => coeff n f) := by
  ext n
  simp [coeff_mk]

/-- Two FPS are equal iff they have the same coefficients (Definition def.fps.fps).
    This is the extensionality principle for FPS. -/
lemma fps_ext_iff (f g : R⟦X⟧) : f = g ↔ ∀ n, coeff n f = coeff n g :=
  ⟨fun h _ => by rw [h], fun h => ext h⟩

/-- The zero FPS is (0, 0, 0, ...) -/
lemma zero_fps_eq : (0 : R⟦X⟧) = PowerSeries.mk (fun _ => 0) := by
  ext n
  simp [coeff_mk]

/-- The one FPS is (1, 0, 0, ...) -/
lemma one_fps_eq : (1 : R⟦X⟧) = PowerSeries.mk (fun n => if n = 0 then 1 else 0) := by
  ext n
  simp [coeff_one, coeff_mk]


/-- (a) Sum of FPS is componentwise (eq. pf.thm.fps.ring.xn(a+b)=)
    Label: pf.thm.fps.ring.xn(a+b)= -/
@[simp]
lemma coeff_add_fps (n : ℕ) (f g : R⟦X⟧) :
    coeff n (f + g) = coeff n f + coeff n g := by
  simp [map_add]

/-- (b) Difference of FPS is componentwise (eq. pf.thm.fps.ring.xn(a-b)=)
    Label: pf.thm.fps.ring.xn(a-b)= -/
@[simp]
lemma coeff_sub_fps (n : ℕ) (f g : R⟦X⟧) :
    coeff n (f - g) = coeff n f - coeff n g := by
  simp [map_sub]

/-- Negation of FPS is componentwise (eq. pf.thm.fps.ring.xn(-a)=)
    Label: pf.thm.fps.ring.xn(-a)= -/
@[simp]
lemma coeff_neg_fps (n : ℕ) (f : R⟦X⟧) :
    coeff n (-f) = -coeff n f := by
  simp [map_neg]

/-- (c) Scalar multiplication (eq. pf.thm.fps.ring.xn(la)=)
    Label: pf.thm.fps.ring.xn(la)= -/
@[simp]
lemma coeff_smul_fps (n : ℕ) (c : R) (f : R⟦X⟧) :
    coeff n (c • f) = c * coeff n f := by
  simp [smul_eq_mul]

/-- (d) Product of FPS uses convolution (eq. pf.thm.fps.ring.xn(ab)=2)
    Label: pf.thm.fps.ring.xn(ab)=2 -/
lemma coeff_mul_fps (n : ℕ) (f g : R⟦X⟧) :
    coeff n (f * g) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff p.1 f * coeff p.2 g :=
  coeff_mul n f g

/-- Alternative form of product formula (eq. pf.thm.fps.ring.xn(ab)=3)
    Label: pf.thm.fps.ring.xn(ab)=3 -/
lemma coeff_mul_fps' (n : ℕ) (f g : R⟦X⟧) :
    coeff n (f * g) = ∑ i ∈ range (n + 1), coeff i f * coeff (n - i) g := by
  rw [coeff_mul_fps]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j g)]

/-- (e) Constant FPS: C a = (a, 0, 0, ...) -/
lemma coeff_C_fps (n : ℕ) (a : R) :
    coeff n (C a : R⟦X⟧) = if n = 0 then a else 0 :=
  coeff_C n a

/-- The constant term of a product is the product of constant terms
    (eq. pf.thm.fps.ring.x0(ab)=)
    Label: pf.thm.fps.ring.x0(ab)= -/
lemma coeff_zero_mul_fps (f g : R⟦X⟧) :
    coeff 0 (f * g) = coeff 0 f * coeff 0 g := by
  rw [coeff_mul_fps]
  simp


/-- (c) Scaling commutes with multiplication (Theorem thm.fps.ring (c)) -/
lemma smul_mul_fps (c : R) (f g : R⟦X⟧) :
    c • (f * g) = (c • f) * g := by
  rw [smul_eq_C_mul, smul_eq_C_mul, mul_assoc]

lemma smul_mul_fps' (c : R) (f g : R⟦X⟧) :
    c • (f * g) = f * (c • g) := by
  rw [smul_eq_C_mul, smul_eq_C_mul, mul_left_comm]

/-- (d) Scaling equals multiplication by constant (Theorem thm.fps.ring (d)) -/
lemma smul_eq_C_mul_fps (c : R) (f : R⟦X⟧) :
    c • f = C c * f :=
  smul_eq_C_mul f c


/-- x = (0, 1, 0, 0, ...) (Definition def.fps.x) -/
@[simp]
lemma X_coeff_one : coeff 1 (X : R⟦X⟧) = 1 := coeff_one_X

lemma X_coeff_ne_one (i : ℕ) (hi : i ≠ 1) : coeff i (X : R⟦X⟧) = 0 := by
  rw [coeff_X]
  simp [hi]


/-- Multiplying by x shifts coefficients: [x^{n+1}](X·f) = [x^n]f (Lemma lem.fps.xa) -/
lemma X_mul_shift (f : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (X * f) = coeff n f :=
  coeff_succ_X_mul n f

/-- Multiplying by x on the right shifts coefficients: [x^{n+1}](f·X) = [x^n]f -/
lemma mul_X_shift (f : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (f * X) = coeff n f :=
  coeff_succ_mul_X n f

/-- The constant term of X * f is 0 (Lemma lem.fps.xa, case n = 0) -/
@[simp]
lemma X_mul_coeff_zero (f : R⟦X⟧) :
    coeff 0 (X * f) = 0 := by
  rw [coeff_mul_fps]
  simp

/-- The constant term of f * X is 0 -/
@[simp]
lemma mul_X_coeff_zero (f : R⟦X⟧) :
    coeff 0 (f * X) = 0 := by
  rw [coeff_mul_fps]
  simp

/-- Complete characterization of multiplication by X (Lemma lem.fps.xa, unified form)

    If f = (a₀, a₁, a₂, ...), then X * f = (0, a₀, a₁, a₂, ...)
    This is equivalent to: [x^n](X·f) = if n = 0 then 0 else [x^{n-1}]f -/
lemma coeff_X_mul (f : R⟦X⟧) (n : ℕ) :
    coeff n (X * f) = if n = 0 then 0 else coeff (n - 1) f := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_succ_X_mul]

/-- Complete characterization of multiplication by X on the right (Lemma lem.fps.xa, variant)

    If f = (a₀, a₁, a₂, ...), then f * X = (0, a₀, a₁, a₂, ...)
    This is equivalent to: [x^n](f·X) = if n = 0 then 0 else [x^{n-1}]f -/
lemma coeff_mul_X (f : R⟦X⟧) (n : ℕ) :
    coeff n (f * X) = if n = 0 then 0 else coeff (n - 1) f := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_succ_mul_X]

/-- X * f equals f with all coefficients shifted by one position (Lemma lem.fps.xa, equality form)

    This directly expresses: X * (a₀, a₁, a₂, ...) = (0, a₀, a₁, a₂, ...) -/
lemma X_mul_eq_shift (f : R⟦X⟧) :
    X * f = PowerSeries.mk (fun n => if n = 0 then 0 else coeff (n - 1) f) := by
  ext n
  rw [coeff_X_mul, coeff_mk]

/-- f * X equals f with all coefficients shifted by one position (Lemma lem.fps.xa, equality form) -/
lemma mul_X_eq_shift (f : R⟦X⟧) :
    f * X = PowerSeries.mk (fun n => if n = 0 then 0 else coeff (n - 1) f) := by
  ext n
  rw [coeff_mul_X, coeff_mk]

/-- X^k * f shifts f by k positions (generalization of Lemma lem.fps.xa)

    If f = (a₀, a₁, a₂, ...), then X^k * f = (0, ..., 0, a₀, a₁, a₂, ...) with k leading zeros. -/
lemma coeff_X_pow_mul (k : ℕ) (f : R⟦X⟧) (n : ℕ) :
    coeff n (X ^ k * f) = if n < k then 0 else coeff (n - k) f := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    cases n with
    | zero => simp
    | succ n =>
      rw [coeff_succ_X_mul, ih]
      simp [Nat.succ_sub_succ]

/-- f * X^k shifts f by k positions (generalization of Lemma lem.fps.xa) -/
lemma coeff_mul_X_pow (k : ℕ) (f : R⟦X⟧) (n : ℕ) :
    coeff n (f * X ^ k) = if n < k then 0 else coeff (n - k) f := by
  rw [mul_comm, coeff_X_pow_mul]


/-- x^k has 1 in position k and 0 elsewhere (Proposition prop.fps.xk) -/
lemma X_pow_coeff (k n : ℕ) :
    coeff n ((X : R⟦X⟧) ^ k) = if n = k then 1 else 0 :=
  coeff_X_pow n k

@[simp]
lemma X_pow_coeff_self (k : ℕ) :
    coeff k ((X : R⟦X⟧) ^ k) = 1 :=
  coeff_X_pow_self k


/-- The family (aₙ x^n)_{n ∈ ℕ} represents the FPS with coefficients (aₙ).
    This is essentially saying PowerSeries.mk a = ∑ a n * X^n
    (Corollary cor.fps.sumakxk) -/
lemma fps_eq_tsum_coeff (f : R⟦X⟧) :
    f = PowerSeries.mk (fun n => coeff n f) := by
  ext n
  simp [coeff_mk]

/-- aₙ x^n has coefficient aₙ in position n and 0 elsewhere -/
lemma coeff_monomial_mul_X_pow (a : R) (k n : ℕ) :
    coeff n (C a * (X : R⟦X⟧) ^ k) = if n = k then a else 0 := by
  simp [coeff_C_mul, coeff_X_pow]

/-- The n-th coefficient of a summable sum is the sum of n-th coefficients.
    (eq. eq.def.fps.summable.sum) -/
lemma coeff_summableFPSSum {ι : Type*} (f : ι → R⟦X⟧) (hf : SummableFPS f) (n : ℕ) :
    coeff n (summableFPSSum f hf) = ∑ᶠ i, coeff n (f i) := by
  simp [summableFPSSum, coeff_mk]

/-- The sum of the coefficients is finite (since the family is summable). -/
lemma summableFPS_finsum_finite {ι : Type*} (f : ι → R⟦X⟧) (hf : SummableFPS f) (n : ℕ) :
    (Function.support (fun i => coeff n (f i))).Finite := hf n

/-- Any subfamily of a summable family of FPS is summable.
    (Proposition prop.fps.summable.sub) -/
lemma summableFPS_subfamily {ι : Type*} {f : ι → R⟦X⟧} (J : Set ι)
    (hf : SummableFPS f) : SummableFPS (fun i : J => f i) := by
  intro n
  have h : {i : J | coeff n (f i) ≠ 0} ⊆ (Subtype.val) ⁻¹' {i | coeff n (f i) ≠ 0} := fun _ hx => hx
  exact Set.Finite.subset ((hf n).preimage Subtype.val_injective.injOn) h

/-- A finite family of FPS is always summable. -/
lemma summableFPS_of_finite {ι : Type*} [Finite ι] (f : ι → R⟦X⟧) : SummableFPS f := by
  intro n
  exact Set.toFinite _

/-- The zero family is summable. -/
lemma summableFPS_zero {ι : Type*} : SummableFPS (fun _ : ι => (0 : R⟦X⟧)) := by
  intro n
  simp

/-- A singleton family is summable. -/
lemma summableFPS_single (f : R⟦X⟧) : SummableFPS (fun _ : Unit => f) :=
  summableFPS_of_finite _

/-- Sum of two summable families is summable. -/
lemma summableFPS_add {ι : Type*} {f g : ι → R⟦X⟧}
    (hf : SummableFPS f) (hg : SummableFPS g) : SummableFPS (fun i => f i + g i) := by
  intro n
  have h : {i | coeff n (f i + g i) ≠ 0} ⊆ {i | coeff n (f i) ≠ 0} ∪ {i | coeff n (g i) ≠ 0} := by
    intro i hi
    simp only [Set.mem_ofPred_eq, map_add, Set.mem_union] at *
    by_contra h
    push Not at h
    simp [h.1, h.2] at hi
  exact Set.Finite.subset (Set.Finite.union (hf n) (hg n)) h

/-- Negation of a summable family is summable. -/
lemma summableFPS_neg {ι : Type*} {f : ι → R⟦X⟧}
    (hf : SummableFPS f) : SummableFPS (fun i => -f i) := by
  intro n
  have h : {i | coeff n (-f i) ≠ 0} = {i | coeff n (f i) ≠ 0} := by
    ext i
    simp only [Set.mem_ofPred_eq, map_neg, neg_ne_zero]
  rw [h]
  exact hf n

/-- Subtraction of two summable families is summable. -/
lemma summableFPS_sub {ι : Type*} {f g : ι → R⟦X⟧}
    (hf : SummableFPS f) (hg : SummableFPS g) : SummableFPS (fun i => f i - g i) := by
  simp only [sub_eq_add_neg]
  exact summableFPS_add hf (summableFPS_neg hg)

/-- Scalar multiple of a summable family is summable. -/
lemma summableFPS_smul {ι : Type*} {f : ι → R⟦X⟧} (c : R)
    (hf : SummableFPS f) : SummableFPS (fun i => c • f i) := by
  intro n
  have h : {i | coeff n (c • f i) ≠ 0} ⊆ {i | coeff n (f i) ≠ 0} := by
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi ⊢
    intro hfi
    simp [hfi] at hi
  exact Set.Finite.subset (hf n) h

/-- An essentially finite family of FPS is summable. -/
lemma summableFPS_of_essentiallyFinite {ι : Type*} (f : ι → R⟦X⟧)
    (hf : {i | f i ≠ 0}.Finite) : SummableFPS f := by
  intro n
  apply Set.Finite.subset hf
  intro i hi
  exact fun h => hi (by simp [h])

/-- The family (C(aₙ) * X^n)_{n ∈ ℕ} is summable for any sequence (aₙ).
    This is the canonical example showing that any FPS can be written as
    an infinite sum ∑_{n ∈ ℕ} aₙ x^n. -/
lemma summableFPS_monomial_family (a : ℕ → R) :
    SummableFPS (fun n => C (a n) * (X : R⟦X⟧) ^ n) := by
  intro m
  have h : {n | coeff m (C (a n) * (X : R⟦X⟧) ^ n) ≠ 0} ⊆ {m} := by
    intro n hn
    simp only [Set.mem_singleton_iff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, Set.mem_ofPred_eq] at hn
    by_contra hne
    have : m ≠ n := fun h => hne h.symm
    simp [this] at hn
  exact Set.Finite.subset (Set.finite_singleton m) h

/-- `EssentiallyFinite` is equivalent to having finite support. -/
lemma essentiallyFinite_iff_support_finite {ι : Type*} (f : ι → R) :
    EssentiallyFinite f ↔ (Function.support f).Finite :=
  _root_.EssentiallyFinite.iff_support_finite

/-- Any subfamily of an essentially finite family is essentially finite.
    (Delegates to `_root_.EssentiallyFinite.subfamily`) -/
lemma essentiallyFinite_subfamily {ι : Type*} {f : ι → R} (J : Set ι)
    (hf : EssentiallyFinite f) : EssentiallyFinite (fun i : J => f i) :=
  _root_.EssentiallyFinite.subfamily J hf

/-- Any finite family is essentially finite.
    (Delegates to `_root_.EssentiallyFinite.of_finite`) -/
lemma essentiallyFinite_of_finite {ι : Type*} [Finite ι] (f : ι → R) :
    EssentiallyFinite f :=
  _root_.EssentiallyFinite.of_finite f

/-- A family indexed by a finite type is essentially finite.
    (Delegates to `_root_.EssentiallyFinite.of_fintype`) -/
lemma essentiallyFinite_fintype {ι : Type*} [Fintype ι] (f : ι → R) :
    EssentiallyFinite f :=
  _root_.EssentiallyFinite.of_fintype f

/-- The constant zero family is essentially finite.
    (Delegates to `_root_.EssentiallyFinite.zero`) -/
lemma essentiallyFinite_zero {ι : Type*} : EssentiallyFinite (fun _ : ι => (0 : R)) :=
  _root_.EssentiallyFinite.zero

/-- Sum of two essentially finite families is essentially finite.
    (Delegates to `_root_.EssentiallyFinite.add`) -/
lemma essentiallyFinite_add {ι : Type*} {f g : ι → R}
    (hf : EssentiallyFinite f) (hg : EssentiallyFinite g) :
    EssentiallyFinite (fun i => f i + g i) :=
  _root_.EssentiallyFinite.add hf hg

/-- Negation of an essentially finite family is essentially finite.
    (Delegates to `_root_.EssentiallyFinite.neg`) -/
lemma essentiallyFinite_neg {ι : Type*} {f : ι → R}
    (hf : EssentiallyFinite f) : EssentiallyFinite (fun i => -f i) :=
  _root_.EssentiallyFinite.neg hf

/-- Subtraction of two essentially finite families is essentially finite.
    (Delegates to `_root_.EssentiallyFinite.sub`) -/
lemma essentiallyFinite_sub {ι : Type*} {f g : ι → R}
    (hf : EssentiallyFinite f) (hg : EssentiallyFinite g) :
    EssentiallyFinite (fun i => f i - g i) :=
  _root_.EssentiallyFinite.sub hf hg

/-- Scalar multiple of an essentially finite family is essentially finite.
    Note: Uses `_root_.EssentiallyFinite.const_mul` with NoZeroDivisors assumption. -/
lemma essentiallyFinite_smul {ι : Type*} {f : ι → R} (c : R) (hf : EssentiallyFinite f) :
    EssentiallyFinite (fun i => c * f i) := by
  apply Set.Finite.subset hf
  intro i hi
  simp only [ne_eq, Function.mem_support] at *
  intro h
  simp [h] at hi

/-- The essentially finite sum equals the Finset sum over the support -/
lemma essFinSum_eq_finset_sum {ι : Type*} (f : ι → R) (hf : EssentiallyFinite f) :
    essFinSum f hf = ∑ i ∈ essFinSupport hf, f i := rfl

/-- If a family has finite support contained in a finset S, the essentially finite sum
    equals the sum over S -/
lemma essFinSum_eq_sum_of_support_subset {ι : Type*} (f : ι → R) (hf : EssentiallyFinite f)
    (S : Finset ι) (hS : essFinSupport hf ⊆ S) :
    essFinSum f hf = ∑ i ∈ S, f i := by
  rw [essFinSum]
  apply Finset.sum_subset hS
  intro x _ hx
  simp only [essFinSupport, Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
  exact hx

/-- The essentially finite sum of a zero family is zero -/
lemma essFinSum_zero {ι : Type*} (hf : EssentiallyFinite (fun _ : ι => (0 : R))) :
    essFinSum (fun _ => 0) hf = 0 := by
  simp [essFinSum, essFinSupport]

/-- The essentially finite sum of a family that is zero everywhere is zero -/
lemma essFinSum_eq_zero_of_forall_zero {ι : Type*} {f : ι → R} (hf : EssentiallyFinite f)
    (h : ∀ i, f i = 0) : essFinSum f hf = 0 := by
  simp [essFinSum, essFinSupport, h]

/-- The essentially finite sum can be computed using any finset containing the support -/
lemma essFinSum_eq_sum_finset {ι : Type*} (f : ι → R) (hf : EssentiallyFinite f)
    (S : Finset ι) (hS : ∀ i, f i ≠ 0 → i ∈ S) :
    essFinSum f hf = ∑ i ∈ S, f i := by
  apply essFinSum_eq_sum_of_support_subset
  intro x hx
  simp only [essFinSupport, Set.Finite.mem_toFinset, Function.mem_support] at hx
  exact hS x hx

/-- The essentially finite sum of a single nonzero element -/
lemma essFinSum_single {ι : Type*} [DecidableEq ι] (i : ι) (a : R) :
    EssentiallyFinite (fun j => if j = i then a else 0) := by
  apply Set.Finite.subset (Set.finite_singleton i)
  intro j hj
  simp only [Function.mem_support, Set.mem_singleton_iff] at *
  by_contra h
  simp [h] at hj

lemma essentiallyFiniteToFinsupp_apply {ι : Type*} (f : ι → R) (hf : EssentiallyFinite f) (i : ι) :
    essentiallyFiniteToFinsupp f hf i = f i := rfl

/-- The essentially finite sum equals the Finsupp sum -/
lemma essFinSum_eq_finsupp_sum {ι : Type*} (f : ι → R) (hf : EssentiallyFinite f) :
    essFinSum f hf = (essentiallyFiniteToFinsupp f hf).sum (fun _ r => r) := by
  simp only [essFinSum, essFinSupport, essentiallyFiniteToFinsupp, Finsupp.ofSupportFinite,
             Finsupp.sum]
  rfl

/-- Additivity: the essentially finite sum of a sum is the sum of essentially finite sums -/
lemma essFinSum_add {ι : Type*} [DecidableEq ι] {f g : ι → R}
    (hf : EssentiallyFinite f) (hg : EssentiallyFinite g)
    (hfg : EssentiallyFinite (fun i => f i + g i)) :
    essFinSum (fun i => f i + g i) hfg = essFinSum f hf + essFinSum g hg := by
  -- The support of f + g is contained in support f ∪ support g
  let S := essFinSupport hf ∪ essFinSupport hg
  have hfS : essFinSupport hf ⊆ S := Finset.subset_union_left
  have hgS : essFinSupport hg ⊆ S := Finset.subset_union_right
  have hfgS : essFinSupport hfg ⊆ S := by
    intro x hx
    simp only [essFinSupport, Set.Finite.mem_toFinset, Function.mem_support] at hx
    simp only [S, Finset.mem_union, essFinSupport, Set.Finite.mem_toFinset, Function.mem_support]
    by_contra h
    push Not at h
    simp [h.1, h.2] at hx
  calc essFinSum (fun i => f i + g i) hfg
      = ∑ i ∈ S, (f i + g i) := by
          apply Finset.sum_subset hfgS
          intro x _ hx
          simp only [essFinSupport, Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
          exact hx
    _ = ∑ i ∈ S, f i + ∑ i ∈ S, g i := Finset.sum_add_distrib
    _ = essFinSum f hf + essFinSum g hg := by
          congr 1
          · symm
            apply Finset.sum_subset hfS
            intro x _ hx
            simp only [essFinSupport, Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
            exact hx
          · symm
            apply Finset.sum_subset hgS
            intro x _ hx
            simp only [essFinSupport, Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
            exact hx

/-- Scalar multiplication: c * (∑ aᵢ) = ∑ (c * aᵢ) -/
lemma essFinSum_smul {ι : Type*} {f : ι → R} (c : R) (hf : EssentiallyFinite f)
    (hcf : EssentiallyFinite (fun i => c * f i)) :
    essFinSum (fun i => c * f i) hcf = c * essFinSum f hf := by
  have hS : essFinSupport hcf ⊆ essFinSupport hf := by
    intro x hx
    simp only [essFinSupport, Set.Finite.mem_toFinset, Function.mem_support] at *
    intro h
    simp [h] at hx
  calc essFinSum (fun i => c * f i) hcf
      = ∑ i ∈ essFinSupport hf, c * f i := by
          apply Finset.sum_subset hS
          intro x _ hx
          simp only [essFinSupport, Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
          simp [hx]
    _ = c * ∑ i ∈ essFinSupport hf, f i := by rw [Finset.mul_sum]
    _ = c * essFinSum f hf := rfl


/-- The Fubini rule for summable FPS families: interchange of summation is valid
    when the family indexed by the product is summable.
    (Proposition prop.fps.summable-sums-rule, discrete Fubini rule)

    Note: The actual sum computation requires Mathlib's topological sum machinery.
    This theorem states that the summability condition on the product implies
    summability of the iterated sums. -/
lemma summableFPS_fubini {ι κ : Type*} {f : ι × κ → R⟦X⟧}
    (hf : SummableFPS f) :
    (∀ i, SummableFPS (fun j => f (i, j))) ∧
    (∀ j, SummableFPS (fun i => f (i, j))) := by
  constructor
  · intro i n
    have : {j | coeff n (f (i, j)) ≠ 0} ⊆ Prod.snd '' {p | coeff n (f p) ≠ 0} := by
      intro j hj
      exact ⟨(i, j), hj, rfl⟩
    exact Set.Finite.subset (Set.Finite.image Prod.snd (hf n)) this
  · intro j n
    have : {i | coeff n (f (i, j)) ≠ 0} ⊆ Prod.fst '' {p | coeff n (f p) ≠ 0} := by
      intro i hi
      exact ⟨(i, j), hi, rfl⟩
    exact Set.Finite.subset (Set.Finite.image Prod.fst (hf n)) this

lemma generatingFunction_coeff (a : ℕ → R) (n : ℕ) :
    coeff n (generatingFunction a) = a n := by
  simp [generatingFunction, coeff_mk]

/-- The generating function of the zero sequence is 0 -/
@[simp]
lemma generatingFunction_zero : generatingFunction (0 : ℕ → R) = 0 := by
  ext n
  simp [generatingFunction, coeff_mk]

/-- The generating function of a sum is the sum of generating functions -/
@[simp]
lemma generatingFunction_add (a b : ℕ → R) :
    generatingFunction (a + b) = generatingFunction a + generatingFunction b := by
  ext n
  simp [generatingFunction, coeff_mk]

/-- The generating function of a negation is the negation of the generating function -/
@[simp]
lemma generatingFunction_neg (a : ℕ → R) :
    generatingFunction (-a) = -generatingFunction a := by
  ext n
  simp [generatingFunction, coeff_mk]

/-- The generating function of a scalar multiple is the scalar multiple of the generating function -/
@[simp]
lemma generatingFunction_smul (c : R) (a : ℕ → R) :
    generatingFunction (c • a) = c • generatingFunction a := by
  ext n
  simp [generatingFunction, coeff_mk, Pi.smul_apply, smul_eq_mul]

/-- Subtraction of generating functions -/
@[simp]
lemma generatingFunction_sub (a b : ℕ → R) :
    generatingFunction (a - b) = generatingFunction a - generatingFunction b := by
  ext n
  simp [generatingFunction, coeff_mk]

/-- The generating function of the indicator function at 0 is 1 -/
@[simp]
lemma generatingFunction_one :
    generatingFunction (fun n => if n = 0 then (1 : R) else 0) = 1 := by
  ext n
  simp [generatingFunction, coeff_mk, coeff_one]


/-- Vandermonde's identity for natural numbers (Proposition prop.binom.vandermonde.NN)
    Label: eq.prop.binom.vandermonde.NN.eq -/
lemma vandermonde_nat (a b n : ℕ) :
    (a + b).choose n = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, a.choose ij.1 * b.choose ij.2 :=
  Nat.add_choose_eq a b n

/-- Alternative form using range -/
lemma vandermonde_nat' (a b n : ℕ) :
    (a + b).choose n = ∑ k ∈ range (n + 1), a.choose k * b.choose (n - k) := by
  rw [vandermonde_nat]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a.choose i * b.choose j)]


/-- Chu-Vandermonde identity for binomial rings (Theorem thm.binom.vandermonde.CC)
    Label: eq.prop.binom.vandermonde.CC.eq

    This generalizes Vandermonde's identity from natural numbers to any binomial ring
    (including ℚ, ℝ, ℂ, and polynomial rings). -/
lemma chuVandermonde {S : Type*} [CommRing S] [BinomialRing S] (a b : S) (n : ℕ) :
    Ring.choose (a + b) n = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, Ring.choose a ij.1 * Ring.choose b ij.2 :=
  Ring.add_choose_eq n (Commute.all a b)

end FPS

end AlgebraicCombinatorics
end


/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma fps_mk_eq_symm_eq
  [CommRing R]
-- given
  (a : ℕ → R) :
-- imply
  PowerSeries.mk a = AlgebraicCombinatorics.FPS.fpsEquivSeq.symm a := by
-- proof
  apply AlgebraicCombinatorics.FPS.fps_mk_eq_symm a

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma fps_coeff_mk_eq
  [CommRing R]
-- given
  (a : ℕ → R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (PowerSeries.mk a) = a n := by
-- proof
  apply AlgebraicCombinatorics.FPS.fps_coeff_mk a n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma fps_eq_mk_coeff_eq
  [CommRing R]
-- given
  (f : PowerSeries R) :
-- imply
  f = PowerSeries.mk (fun n => PowerSeries.coeff n f) := by
-- proof
  apply AlgebraicCombinatorics.FPS.fps_eq_mk_coeff f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma pv_fps_ext_iff
  [CommRing R]
-- given
  (f g : PowerSeries R) :
-- imply
  f = g ↔ ∀ n, PowerSeries.coeff n f = PowerSeries.coeff n g := by
-- proof
  apply AlgebraicCombinatorics.FPS.fps_ext_iff f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma pv_zero_fps_eq
  [CommRing R] :
-- imply
  (0 : PowerSeries R) = PowerSeries.mk (fun _ => 0) := by
-- proof
  apply AlgebraicCombinatorics.FPS.zero_fps_eq

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma pv_one_fps_eq
  [CommRing R] :
-- imply
  (1 : PowerSeries R) = PowerSeries.mk (fun n => if n = 0 then 1 else 0) := by
-- proof
  apply AlgebraicCombinatorics.FPS.one_fps_eq

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_add_fps_eq
  [CommRing R]
-- given
  (n : ℕ)
  (f g : PowerSeries R) :
-- imply
  PowerSeries.coeff n (f + g) = PowerSeries.coeff n f + PowerSeries.coeff n g := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_add_fps n f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_sub_fps_eq
  [CommRing R]
-- given
  (n : ℕ)
  (f g : PowerSeries R) :
-- imply
  PowerSeries.coeff n (f - g) = PowerSeries.coeff n f - PowerSeries.coeff n g := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_sub_fps n f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_neg_fps_eq
  [CommRing R]
-- given
  (n : ℕ)
  (f : PowerSeries R) :
-- imply
  PowerSeries.coeff n (-f) = -PowerSeries.coeff n f := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_neg_fps n f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_smul_fps_eq
  [CommRing R]
-- given
  (n : ℕ)
  (c : R)
  (f : PowerSeries R) :
-- imply
  PowerSeries.coeff n (c • f) = c * PowerSeries.coeff n f := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_smul_fps n c f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_mul_fps_eq
  [CommRing R]
-- given
  (n : ℕ)
  (f g : PowerSeries R) :
-- imply
  PowerSeries.coeff n (f * g) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_mul_fps n f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_mul_fps'_eq
  [CommRing R]
-- given
  (n : ℕ)
  (f g : PowerSeries R) :
-- imply
  PowerSeries.coeff n (f * g) = ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i f * PowerSeries.coeff (n - i) g := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_mul_fps' n f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_C_fps_eq
  [CommRing R]
-- given
  (n : ℕ)
  (a : R) :
-- imply
  PowerSeries.coeff n (PowerSeries.C a : PowerSeries R) = if n = 0 then a else 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_C_fps n a

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_zero_mul_fps_eq
  [CommRing R]
-- given
  (f g : PowerSeries R) :
-- imply
  PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_zero_mul_fps f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma smul_mul_fps_eq
  [CommRing R]
-- given
  (c : R)
  (f g : PowerSeries R) :
-- imply
  c • (f * g) = (c • f) * g := by
-- proof
  apply AlgebraicCombinatorics.FPS.smul_mul_fps c f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma smul_mul_fps'_eq
  [CommRing R]
-- given
  (c : R)
  (f g : PowerSeries R) :
-- imply
  c • (f * g) = f * (c • g) := by
-- proof
  apply AlgebraicCombinatorics.FPS.smul_mul_fps' c f g

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma smul_eq_C_mul_fps_eq
  [CommRing R]
-- given
  (c : R)
  (f : PowerSeries R) :
-- imply
  c • f = PowerSeries.C c * f := by
-- proof
  apply AlgebraicCombinatorics.FPS.smul_eq_C_mul_fps c f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma X_coeff_one_eq
  [CommRing R] :
-- imply
  PowerSeries.coeff 1 (PowerSeries.X : PowerSeries R) = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.X_coeff_one

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma X_coeff_ne_one_eq
  [CommRing R]
-- given
  (i : ℕ)
  (hi : i ≠ 1) :
-- imply
  PowerSeries.coeff i (PowerSeries.X : PowerSeries R) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.X_coeff_ne_one i hi

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma X_mul_shift_eq
  [CommRing R]
-- given
  (f : PowerSeries R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff (n + 1) (PowerSeries.X * f) = PowerSeries.coeff n f := by
-- proof
  apply AlgebraicCombinatorics.FPS.X_mul_shift f n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma mul_X_shift_eq
  [CommRing R]
-- given
  (f : PowerSeries R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff (n + 1) (f * PowerSeries.X) = PowerSeries.coeff n f := by
-- proof
  apply AlgebraicCombinatorics.FPS.mul_X_shift f n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma X_mul_coeff_zero_eq
  [CommRing R]
-- given
  (f : PowerSeries R) :
-- imply
  PowerSeries.coeff 0 (PowerSeries.X * f) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.X_mul_coeff_zero f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma mul_X_coeff_zero_eq
  [CommRing R]
-- given
  (f : PowerSeries R) :
-- imply
  PowerSeries.coeff 0 (f * PowerSeries.X) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.mul_X_coeff_zero f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_X_mul_eq
  [CommRing R]
-- given
  (f : PowerSeries R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (PowerSeries.X * f) = if n = 0 then 0 else PowerSeries.coeff (n - 1) f := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_X_mul f n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_mul_X_eq
  [CommRing R]
-- given
  (f : PowerSeries R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (f * PowerSeries.X) = if n = 0 then 0 else PowerSeries.coeff (n - 1) f := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_mul_X f n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma X_mul_eq_shift_eq
  [CommRing R]
-- given
  (f : PowerSeries R) :
-- imply
  PowerSeries.X * f = PowerSeries.mk (fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) f) := by
-- proof
  apply AlgebraicCombinatorics.FPS.X_mul_eq_shift f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma mul_X_eq_shift_eq
  [CommRing R]
-- given
  (f : PowerSeries R) :
-- imply
  f * PowerSeries.X = PowerSeries.mk (fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) f) := by
-- proof
  apply AlgebraicCombinatorics.FPS.mul_X_eq_shift f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_X_pow_mul_eq
  [CommRing R]
-- given
  (k : ℕ)
  (f : PowerSeries R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (PowerSeries.X ^ k * f) = if n < k then 0 else PowerSeries.coeff (n - k) f := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_X_pow_mul k f n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_mul_X_pow_eq
  [CommRing R]
-- given
  (k : ℕ)
  (f : PowerSeries R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (f * PowerSeries.X ^ k) = if n < k then 0 else PowerSeries.coeff (n - k) f := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_mul_X_pow k f n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma X_pow_coeff_eq
  [CommRing R]
-- given
  (k n : ℕ) :
-- imply
  PowerSeries.coeff n ((PowerSeries.X : PowerSeries R) ^ k) = if n = k then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.X_pow_coeff k n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma X_pow_coeff_self_eq
  [CommRing R]
-- given
  (k : ℕ) :
-- imply
  PowerSeries.coeff k ((PowerSeries.X : PowerSeries R) ^ k) = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.X_pow_coeff_self k

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma fps_eq_tsum_coeff_eq
  [CommRing R]
-- given
  (f : PowerSeries R) :
-- imply
  f = PowerSeries.mk (fun n => PowerSeries.coeff n f) := by
-- proof
  apply AlgebraicCombinatorics.FPS.fps_eq_tsum_coeff f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_monomial_mul_X_pow_eq
  [CommRing R]
-- given
  (a : R)
  (k n : ℕ) :
-- imply
  PowerSeries.coeff n (PowerSeries.C a * (PowerSeries.X : PowerSeries R) ^ k) = if n = k then a else 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_monomial_mul_X_pow a k n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma coeff_summable_fps_sum_eq
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → PowerSeries R)
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (AlgebraicCombinatorics.FPS.summableFPSSum f hf) = finsum fun i => PowerSeries.coeff n (f i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.coeff_summableFPSSum f hf n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_finsum_finite_is
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → PowerSeries R)
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f)
  (n : ℕ) :
-- imply
  (Function.support (fun i => PowerSeries.coeff n (f i))).Finite := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_finsum_finite f hf n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_subfamily_is
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → PowerSeries R}
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f)
  (J : Set ι) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun i : J => f i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_subfamily J hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_of_finite_is
  [CommRing R]
  [Finite ι]
-- given
  (f : ι → PowerSeries R) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS f := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_of_finite f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_zero_is
  [CommRing R]
-- given
  (ι : Type*) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun _ : ι => (0 : PowerSeries R)) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_zero

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_single_is
  [CommRing R]
-- given
  (f : PowerSeries R) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun _ : Unit => f) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_single f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_add_is
  [CommRing R]
-- given
  {ι : Type*}
  {f g : ι → PowerSeries R}
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f)
  (hg : AlgebraicCombinatorics.FPS.SummableFPS g) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun i => f i + g i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_add hf hg

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_neg_is
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → PowerSeries R}
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun i => -f i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_neg hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_sub_is
  [CommRing R]
-- given
  {ι : Type*}
  {f g : ι → PowerSeries R}
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f)
  (hg : AlgebraicCombinatorics.FPS.SummableFPS g) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun i => f i - g i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_sub hf hg

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_smul_is
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → PowerSeries R}
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f)
  (c : R) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun i => c • f i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_smul c hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_of_essentially_finite_is
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → PowerSeries R)
  (hf : {i | f i ≠ 0}.Finite) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS f := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_of_essentiallyFinite f hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_monomial_family_is
  [CommRing R]
-- given
  (a : ℕ → R) :
-- imply
  AlgebraicCombinatorics.FPS.SummableFPS (fun n => PowerSeries.C (a n) * (PowerSeries.X : PowerSeries R) ^ n) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_monomial_family a

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_iff_support_finite_iff
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → R) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite f ↔ (Function.support f).Finite := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_iff_support_finite f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_subfamily_is
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → R}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (J : Set ι) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite (fun i : J => f i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_subfamily J hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_of_finite_is
  [CommRing R]
  [Finite ι]
-- given
  (f : ι → R) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite f := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_of_finite f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_fintype_is
  [CommRing R]
  [Fintype ι]
-- given
  (f : ι → R) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite f := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_fintype f

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_zero_is
  [CommRing R]
-- given
  (ι : Type*) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite (fun _ : ι => (0 : R)) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_zero

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_add_is
  [CommRing R]
-- given
  {ι : Type*}
  {f g : ι → R}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (hg : AlgebraicCombinatorics.FPS.EssentiallyFinite g) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite (fun i => f i + g i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_add hf hg

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_neg_is
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → R}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite (fun i => -f i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_neg hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_sub_is
  [CommRing R]
-- given
  {ι : Type*}
  {f g : ι → R}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (hg : AlgebraicCombinatorics.FPS.EssentiallyFinite g) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite (fun i => f i - g i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_sub hf hg

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_smul_is
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → R}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (c : R) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite (fun i => c * f i) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFinite_smul c hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_eq_finset_sum_eq
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → R)
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum f hf = ∑ i ∈ AlgebraicCombinatorics.FPS.essFinSupport hf, f i := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_eq_finset_sum f hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_eq_sum_of_support_subset_eq
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → R)
  (S : Finset ι)
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (hS : AlgebraicCombinatorics.FPS.essFinSupport hf ⊆ S) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum f hf = ∑ i ∈ S, f i := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_eq_sum_of_support_subset f hf S hS

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_zero_eq
  [CommRing R]
-- given
  {ι : Type*}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite (fun _ : ι => (0 : R))) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum (fun _ => 0) hf = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_zero hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_eq_zero_of_forall_zero_eq
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → R}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (h : ∀ i, f i = 0) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum f hf = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_eq_zero_of_forall_zero hf h

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_eq_sum_finset_eq
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → R)
  (S : Finset ι)
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (hS : ∀ i, f i ≠ 0 → i ∈ S) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum f hf = ∑ i ∈ S, f i := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_eq_sum_finset f hf S hS

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_single_is
  [CommRing R]
  [DecidableEq ι]
-- given
  (i : ι)
  (a : R) :
-- imply
  AlgebraicCombinatorics.FPS.EssentiallyFinite (fun j => if j = i then a else 0) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_single i a

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma essentially_finite_to_finsupp_apply_eq
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → R)
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (i : ι) :
-- imply
  AlgebraicCombinatorics.FPS.essentiallyFiniteToFinsupp f hf i = f i := by
-- proof
  apply AlgebraicCombinatorics.FPS.essentiallyFiniteToFinsupp_apply f hf i

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_eq_finsupp_sum_eq
  [CommRing R]
-- given
  {ι : Type*}
  (f : ι → R)
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum f hf = (AlgebraicCombinatorics.FPS.essentiallyFiniteToFinsupp f hf).sum (fun _ r => r) := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_eq_finsupp_sum f hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_add_eq
  [CommRing R]
  [DecidableEq ι]
-- given
  {f g : ι → R}
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (hg : AlgebraicCombinatorics.FPS.EssentiallyFinite g)
  (hfg : AlgebraicCombinatorics.FPS.EssentiallyFinite (fun i => f i + g i)) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum (fun i => f i + g i) hfg = AlgebraicCombinatorics.FPS.essFinSum f hf + AlgebraicCombinatorics.FPS.essFinSum g hg := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_add hf hg hfg

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma ess_fin_sum_smul_eq
  [CommRing R]
-- given
  {ι : Type*}
  {f : ι → R}
  (c : R)
  (hf : AlgebraicCombinatorics.FPS.EssentiallyFinite f)
  (hcf : AlgebraicCombinatorics.FPS.EssentiallyFinite (fun i => c * f i)) :
-- imply
  AlgebraicCombinatorics.FPS.essFinSum (fun i => c * f i) hcf = c * AlgebraicCombinatorics.FPS.essFinSum f hf := by
-- proof
  apply AlgebraicCombinatorics.FPS.essFinSum_smul c hf hcf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma summable_fps_fubini_is
  [CommRing R]
-- given
  {ι κ : Type*}
  {f : ι × κ → PowerSeries R}
  (hf : AlgebraicCombinatorics.FPS.SummableFPS f) :
-- imply
  (∀ i, AlgebraicCombinatorics.FPS.SummableFPS (fun j => f (i, j))) ∧ (∀ j, AlgebraicCombinatorics.FPS.SummableFPS (fun i => f (i, j))) := by
-- proof
  apply AlgebraicCombinatorics.FPS.summableFPS_fubini hf

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma generating_function_coeff_eq
  [CommRing R]
-- given
  (a : ℕ → R)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (AlgebraicCombinatorics.FPS.generatingFunction a) = a n := by
-- proof
  apply AlgebraicCombinatorics.FPS.generatingFunction_coeff a n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma generating_function_zero_eq
  [CommRing R] :
-- imply
  AlgebraicCombinatorics.FPS.generatingFunction (0 : ℕ → R) = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.generatingFunction_zero

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma generating_function_add_eq
  [CommRing R]
-- given
  (a b : ℕ → R) :
-- imply
  AlgebraicCombinatorics.FPS.generatingFunction (a + b) = AlgebraicCombinatorics.FPS.generatingFunction a + AlgebraicCombinatorics.FPS.generatingFunction b := by
-- proof
  apply AlgebraicCombinatorics.FPS.generatingFunction_add a b

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma generating_function_neg_eq
  [CommRing R]
-- given
  (a : ℕ → R) :
-- imply
  AlgebraicCombinatorics.FPS.generatingFunction (-a) = -AlgebraicCombinatorics.FPS.generatingFunction a := by
-- proof
  apply AlgebraicCombinatorics.FPS.generatingFunction_neg a

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma generating_function_smul_eq
  [CommRing R]
-- given
  (c : R)
  (a : ℕ → R) :
-- imply
  AlgebraicCombinatorics.FPS.generatingFunction (c • a) = c • AlgebraicCombinatorics.FPS.generatingFunction a := by
-- proof
  apply AlgebraicCombinatorics.FPS.generatingFunction_smul c a

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma generating_function_sub_eq
  [CommRing R]
-- given
  (a b : ℕ → R) :
-- imply
  AlgebraicCombinatorics.FPS.generatingFunction (a - b) = AlgebraicCombinatorics.FPS.generatingFunction a - AlgebraicCombinatorics.FPS.generatingFunction b := by
-- proof
  apply AlgebraicCombinatorics.FPS.generatingFunction_sub a b

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma generating_function_one_eq
  [CommRing R] :
-- imply
  AlgebraicCombinatorics.FPS.generatingFunction (fun n => if n = 0 then (1 : R) else 0) = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.generatingFunction_one

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma vandermonde_nat_eq
-- given
  (a b n : ℕ) :
-- imply
  (a + b).choose n = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, a.choose ij.1 * b.choose ij.2 := by
-- proof
  apply AlgebraicCombinatorics.FPS.vandermonde_nat a b n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma vandermonde_nat'_eq
-- given
  (a b n : ℕ) :
-- imply
  (a + b).choose n = ∑ k ∈ Finset.range (n + 1), a.choose k * b.choose (n - k) := by
-- proof
  apply AlgebraicCombinatorics.FPS.vandermonde_nat' a b n

/--
[FPSDefinition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPSDefinition.lean)
-/
@[path]
private lemma chu_vandermonde_eq
  [CommRing S]
  [BinomialRing S]
-- given
  (a b : S)
  (n : ℕ) :
-- imply
  Ring.choose (a + b) n = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, Ring.choose a ij.1 * Ring.choose b ij.2 := by
-- proof
  apply AlgebraicCombinatorics.FPS.chuVandermonde a b n


-- created on 2026-10-12
