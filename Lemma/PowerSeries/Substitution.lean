import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.RingTheory.PowerSeries.Substitution
import Lemma.PowerSeries.FPSDefinition
open PowerSeries
open scoped BigOperators
open AlgebraicCombinatorics
open AlgebraicCombinatorics.FPS (SummableFPS summableFPSSum)


section
-- ac-theorems


namespace AlgebraicCombinatorics

open PowerSeries
open AlgebraicCombinatorics.FPS (SummableFPS summableFPSSum coeff_summableFPSSum)

variable {K : Type*} [CommRing K]

/-- The composition f[g] equals the Mathlib substitution. -/
lemma fps_comp_eq_subst (f g : K⟦X⟧) (hg : constantCoeff g = 0) :
    fps_comp f g hg = PowerSeries.subst g f := rfl

/-- **Definition 7.3.1** (def.fps.subs) - Coefficient formula
The n-th coefficient of f[g] is the (finitely supported) sum ∑_{d∈ℕ} fₐ · [xⁿ](g^d).

This is the explicit formula from Definition 7.3.1: f[g] = ∑_{n∈ℕ} fₙ gⁿ,
expressed at the coefficient level. -/
lemma fps_comp_coeff (f g : K⟦X⟧) (hg : constantCoeff g = 0) (n : ℕ) :
    coeff n (PowerSeries.subst g f) = finsum (fun d ↦ coeff d f * coeff n (g ^ d)) := by
  have ha := HasSubst.of_constantCoeff_zero' hg
  rw [coeff_subst' ha f n]
  rfl


/-- **Proposition 7.3.3(a)** (prop.fps.subs.wd)
For each n∈ℕ, the first n coefficients of the FPS g^n are 0 when g has constant term 0.

This follows from g = x·h for some h, so g^n = x^n · h^n. -/
lemma fps_subs_wd_firstCoeffs (g : K⟦X⟧) (hg : constantCoeff g = 0) (n : ℕ) (k : ℕ) (hk : k < n) :
    coeff k (g ^ n) = 0 := by
  have h_order : (n : ℕ∞) ≤ (g ^ n).order := le_order_pow_of_constantCoeff_eq_zero n hg
  exact coeff_of_lt_order k (lt_of_lt_of_le (Nat.cast_lt.mpr hk) h_order)

/-- **Definition 7.3.1** (def.fps.subs) - Alternative coefficient formula
For any fixed n, the sum ∑_{d∈ℕ} fₐ · [xⁿ](g^d) is actually finite,
since [xⁿ](g^d) = 0 for d > n when g has constant term 0. -/
lemma fps_comp_coeff_finite (f g : K⟦X⟧) (hg : constantCoeff g = 0) (n : ℕ) :
    coeff n (PowerSeries.subst g f) = ∑ d ∈ Finset.range (n + 1), coeff d f * coeff n (g ^ d) := by
  rw [fps_comp_coeff f g hg n]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  push Not at h
  have hdn : n < d := Nat.lt_of_succ_le h
  have hz : coeff n (g ^ d) = 0 := fps_subs_wd_firstCoeffs g hg d n hdn
  rw [Function.mem_support] at hd
  rw [hz, mul_zero] at hd
  exact hd rfl

/-- **Proposition 7.3.3(b)** (prop.fps.subs.wd)
The family (fₙ gⁿ)_{n∈ℕ} is summable, i.e., for each coefficient position m,
only finitely many terms contribute.

In Mathlib, this is built into the definition of `PowerSeries.subst` via `HasSubst`. -/
lemma fps_subs_wd_summable (_f g : K⟦X⟧) (hg : constantCoeff g = 0) :
    HasSubst g :=
  HasSubst.of_constantCoeff_zero' hg

/-- **Proposition 7.3.3(c)** (prop.fps.subs.wd)
The constant coefficient of f[g] equals f₀. -/
lemma fps_subs_wd_constCoeff (f g : K⟦X⟧) (hg : constantCoeff g = 0) :
    constantCoeff (PowerSeries.subst g f) = constantCoeff f := by
  have ha := HasSubst.of_constantCoeff_zero' hg
  rw [show constantCoeff (PowerSeries.subst g f) =
      MvPowerSeries.constantCoeff (PowerSeries.subst g f) from rfl]
  rw [constantCoeff_subst ha]
  rw [finsum_eq_single (fun d ↦ coeff d f • MvPowerSeries.constantCoeff (g ^ d)) 0]
  · simp [MvPowerSeries.constantCoeff_one]
  · intro d hd
    simp only [smul_eq_mul]
    have h1 : MvPowerSeries.constantCoeff (g ^ d) = (MvPowerSeries.constantCoeff g) ^ d :=
      map_pow _ _ _
    have h2 : MvPowerSeries.constantCoeff g = (0 : K) := hg
    simp only [h1, h2, zero_pow hd, mul_zero]

/-- Substituting into 0 gives 0. -/
@[simp] lemma subst_zero (g : K⟦X⟧) (hg : constantCoeff g = 0) :
    PowerSeries.subst g (0 : K⟦X⟧) = 0 := by
  have ha := HasSubst.of_constantCoeff_zero' hg
  rw [← coe_substAlgHom ha]
  simp

/-- Substituting into 1 gives 1. -/
@[simp] lemma subst_one (g : K⟦X⟧) (hg : constantCoeff g = 0) :
    PowerSeries.subst g (1 : K⟦X⟧) = 1 := by
  have ha := HasSubst.of_constantCoeff_zero' hg
  rw [← coe_substAlgHom ha]
  simp


/-- **Lemma 7.3.5** (lem.fps.fg-coeffs-0)
If the first k coefficients of f are 0, then the first k coefficients of f ∘ g are 0. -/
lemma fps_fg_coeffs_zero (f g : K⟦X⟧) (hg : constantCoeff g = 0)
    (k : ℕ) (hf : ∀ m < k, coeff m f = 0) :
    ∀ m < k, coeff m (PowerSeries.subst g f) = 0 := by
  intro m hm
  have hf_order : (k : ℕ∞) ≤ f.order := by
    apply le_order
    intro n hn
    exact hf n (Nat.cast_lt.mp hn)
  have hg_order : 1 ≤ g.order := one_le_order_iff_constCoeff_eq_zero.mpr hg
  have hg_order' : 1 ≤ MvPowerSeries.order g := by rw [← order_eq_order]; exact hg_order
  have h_order : (k : ℕ∞) ≤ order (PowerSeries.subst g f) := by
    rw [order_eq_order]
    calc MvPowerSeries.order (PowerSeries.subst g f : MvPowerSeries Unit K)
        ≥ MvPowerSeries.order g * f.order :=
            le_order_subst g (HasSubst.of_constantCoeff_zero' hg) f
      _ ≥ 1 * f.order := mul_le_mul_left hg_order' f.order
      _ = f.order := one_mul _
      _ ≥ k := hf_order
  exact coeff_of_lt_order m (lt_of_lt_of_le (Nat.cast_lt.mpr hm) h_order)


/-- **Proposition 7.3.4(a)** (prop.fps.subs.rules)
(f₁ + f₂) ∘ g = f₁ ∘ g + f₂ ∘ g -/
lemma fps_subs_add (f₁ f₂ g : K⟦X⟧) (hg : constantCoeff g = 0) :
    PowerSeries.subst g (f₁ + f₂) = PowerSeries.subst g f₁ + PowerSeries.subst g f₂ :=
  subst_add (HasSubst.of_constantCoeff_zero' hg) f₁ f₂

/-- **Proposition 7.3.4(b)** (prop.fps.subs.rules)
(f₁ · f₂) ∘ g = (f₁ ∘ g) · (f₂ ∘ g) -/
lemma fps_subs_mul (f₁ f₂ g : K⟦X⟧) (hg : constantCoeff g = 0) :
    PowerSeries.subst g (f₁ * f₂) = PowerSeries.subst g f₁ * PowerSeries.subst g f₂ :=
  subst_mul (HasSubst.of_constantCoeff_zero' hg) f₁ f₂

/-- **Proposition 7.3.4(c)** (prop.fps.subs.rules)
(f₁ / f₂) ∘ g = (f₁ ∘ g) / (f₂ ∘ g) when f₂ is invertible.

Note: Division of power series requires working over a field. We state this
for the case where K is a field and f₂ has nonzero constant coefficient.

In the source, this is stated as: if f₂ is invertible (i.e., has nonzero constant term),
then f₂ ∘ g is automatically invertible and the division rule holds. -/
lemma fps_subs_div {K : Type*} [Field K] (f₁ f₂ g : K⟦X⟧) (hg : constantCoeff g = 0)
    (hf₂ : constantCoeff f₂ ≠ 0) :
    PowerSeries.subst g f₁ * (PowerSeries.subst g f₂)⁻¹ =
    PowerSeries.subst g (f₁ * f₂⁻¹) := by
  have ha := HasSubst.of_constantCoeff_zero' hg
  -- First show that subst g f₂ has nonzero constant coefficient
  have hf₂g : constantCoeff (PowerSeries.subst g f₂) ≠ 0 := by
    rw [fps_subs_wd_constCoeff f₂ g hg]
    exact hf₂
  -- Use the multiplicative property
  rw [subst_mul ha]
  congr 1
  -- Need to show subst g f₂⁻¹ = (subst g f₂)⁻¹
  -- subst g (f₂ * f₂⁻¹) = subst g 1 = 1
  have h1 : PowerSeries.subst g (f₂ * f₂⁻¹) = 1 := by
    rw [PowerSeries.mul_inv_cancel f₂ hf₂]
    rw [← coe_substAlgHom ha, map_one]
  -- Also subst g (f₂ * f₂⁻¹) = subst g f₂ * subst g f₂⁻¹
  have h2 : PowerSeries.subst g (f₂ * f₂⁻¹) = PowerSeries.subst g f₂ * PowerSeries.subst g f₂⁻¹ :=
    subst_mul ha f₂ f₂⁻¹
  -- So subst g f₂ * subst g f₂⁻¹ = 1
  rw [h1] at h2
  -- Therefore subst g f₂⁻¹ = (subst g f₂)⁻¹
  have h3 : PowerSeries.subst g f₂ * PowerSeries.subst g f₂⁻¹ = 1 := h2.symm
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one hf₂g]
  rw [mul_comm]
  exact h3

/-- **Proposition 7.3.4(d)** (prop.fps.subs.rules)
f^k ∘ g = (f ∘ g)^k -/
lemma fps_subs_pow (f g : K⟦X⟧) (hg : constantCoeff g = 0) (k : ℕ) :
    PowerSeries.subst g (f ^ k) = (PowerSeries.subst g f) ^ k :=
  subst_pow (HasSubst.of_constantCoeff_zero' hg) f k

/-- **Proposition 7.3.4(e)** (prop.fps.subs.rules)
(f ∘ g) ∘ h = f ∘ (g ∘ h), and [x⁰](g ∘ h) = 0.

Part 1: The constant coefficient of g ∘ h is 0. -/
lemma fps_subs_assoc_constCoeff (g h : K⟦X⟧) (hg : constantCoeff g = 0) (hh : constantCoeff h = 0) :
    constantCoeff (PowerSeries.subst h g) = 0 := by
  rw [fps_subs_wd_constCoeff g h hh, hg]

/-- **Proposition 7.3.4(e)** (prop.fps.subs.rules)
(f ∘ g) ∘ h = f ∘ (g ∘ h)

Part 2: Associativity of composition. -/
lemma fps_subs_assoc (f g h : K⟦X⟧) (hg : constantCoeff g = 0) (hh : constantCoeff h = 0) :
    PowerSeries.subst h (PowerSeries.subst g f) =
    PowerSeries.subst (PowerSeries.subst h g) f := by
  have ha_g := HasSubst.of_constantCoeff_zero' hg
  have ha_h := HasSubst.of_constantCoeff_zero' hh
  exact subst_comp_subst_apply ha_g ha_h f

/-- **Proposition 7.3.4(f)** (prop.fps.subs.rules)
a ∘ g = a for any constant a ∈ K. -/
lemma fps_subs_const (a : K) (g : K⟦X⟧) (hg : constantCoeff g = 0) :
    PowerSeries.subst g (C a) = C a := by
  have ha := HasSubst.of_constantCoeff_zero' hg
  rw [← coe_substAlgHom ha]
  exact (substAlgHom ha).commutes a

/-- **Proposition 7.3.4(g)** (prop.fps.subs.rules)
X ∘ g = g -/
lemma fps_subs_X_left (g : K⟦X⟧) (hg : constantCoeff g = 0) :
    PowerSeries.subst g (X : K⟦X⟧) = g :=
  subst_X (HasSubst.of_constantCoeff_zero' hg)

/-- Substituting X into g gives g back. Simp-lemma alias for `fps_subs_X_left`. -/
@[simp] lemma subst_X' (g : K⟦X⟧) (hg : constantCoeff g = 0) :
    PowerSeries.subst g (X : K⟦X⟧) = g :=
  fps_subs_X_left g hg

/-- **Proposition 7.3.4(g)** (prop.fps.subs.rules)
g ∘ X = g -/
lemma fps_subs_X_right (g : K⟦X⟧) :
    PowerSeries.subst X g = g := by
  have ha : HasSubst (X : K⟦X⟧) := HasSubst.X'
  ext n
  rw [coeff_subst' ha g n]
  simp only [coeff_X_pow, smul_eq_mul]
  rw [finsum_eq_single _ n (fun d hd => by simp [hd.symm])]
  simp

/-- **Proposition 7.3.4(h)** (prop.fps.subs.rules) - Finite sum version
For a finite sum (∑ᵢ∈s fᵢ), we have (∑ᵢ∈s fᵢ) ∘ g = ∑ᵢ∈s (fᵢ ∘ g). -/
lemma fps_subs_sum {ι : Type*} (s : Finset ι) (f : ι → K⟦X⟧) (g : K⟦X⟧)
    (hg : constantCoeff g = 0) :
    PowerSeries.subst g (∑ i ∈ s, f i) = ∑ i ∈ s, PowerSeries.subst g (f i) := by
  have ha := HasSubst.of_constantCoeff_zero' hg
  rw [← coe_substAlgHom ha, map_sum]


/-- **Proposition 7.3.4(h)** (prop.fps.subs.rules) - Summability preservation
If (fᵢ)_{i∈I} is a summable family and g has constant term 0,
then (fᵢ ∘ g)_{i∈I} is also summable.

The key insight is that [x^n](fᵢ ∘ g) only depends on [x^0]fᵢ, ..., [x^n]fᵢ.
If all these are 0, then [x^n](fᵢ ∘ g) = 0. So the set of i with
[x^n](fᵢ ∘ g) ≠ 0 is contained in the finite union ⋃_{k≤n} {i | [x^k]fᵢ ≠ 0}. -/
lemma fps_subs_summable {ι : Type*} (f : ι → K⟦X⟧) (g : K⟦X⟧)
    (hg : constantCoeff g = 0) (hf : SummableFPS f) :
    SummableFPS (fun i => PowerSeries.subst g (f i)) := by
  intro n
  have ha := HasSubst.of_constantCoeff_zero' hg
  -- The set of i where [x^n](fᵢ ∘ g) ≠ 0 is contained in the union of
  -- {i | [x^k]fᵢ ≠ 0} for k = 0, 1, ..., n
  have h_union : {i | coeff n (PowerSeries.subst g (f i)) ≠ 0} ⊆
      ⋃ k ∈ Finset.range (n + 1), {i | coeff k (f i) ≠ 0} := by
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq]
    by_contra h
    push Not at h
    have hfi : ∀ k ≤ n, coeff k (f i) = 0 := fun k hk => h k (Nat.lt_succ_of_le hk)
    have heq : coeff n (PowerSeries.subst g (f i)) =
        ∑ᶠ d, coeff d (f i) * coeff n (g ^ d) := by
      rw [coeff_subst' ha (f i) n]
      simp only [smul_eq_mul]
    rw [heq] at hi
    have hz : ∀ d, coeff d (f i) * coeff n (g ^ d) = 0 := by
      intro d
      by_cases hd : d ≤ n
      · simp [hfi d hd]
      · push Not at hd
        have hgd : coeff n (g ^ d) = 0 := by
          have h_order : (d : ℕ∞) ≤ (g ^ d).order := le_order_pow_of_constantCoeff_eq_zero d hg
          exact coeff_of_lt_order n (lt_of_lt_of_le (Nat.cast_lt.mpr hd) h_order)
        simp [hgd]
    simp only [finsum_eq_zero_of_forall_eq_zero hz, ne_eq, not_true_eq_false] at hi
  apply Set.Finite.subset _ h_union
  refine Set.Finite.biUnion ?_ ?_
  · simp
  · intro k _
    exact hf k

/-- **Proposition 7.3.4(h)** (prop.fps.subs.rules) - Infinite sum version
For a summable family (fᵢ)_{i∈I}, we have (∑ᵢ fᵢ) ∘ g = ∑ᵢ (fᵢ ∘ g).

This is the full infinite sum version of the substitution rule. The proof uses
the distributive law for multiplication over infinite sums and Fubini's theorem
for essentially finite double sums. -/
lemma fps_subs_summableFPSSum {ι : Type*} (f : ι → K⟦X⟧) (g : K⟦X⟧)
    (hg : constantCoeff g = 0) (hf : SummableFPS f) :
    PowerSeries.subst g (summableFPSSum f hf) =
    summableFPSSum (fun i => PowerSeries.subst g (f i)) (fps_subs_summable f g hg hf) := by
  have ha := HasSubst.of_constantCoeff_zero' hg
  ext n
  rw [coeff_summableFPSSum]
  rw [coeff_subst' ha]
  simp only [smul_eq_mul]
  -- LHS: ∑ᶠ d, [x^d](∑ᶠ i, fᵢ) * [x^n](g^d)
  -- RHS: ∑ᶠ i, [x^n](fᵢ ∘ g)
  simp only [coeff_summableFPSSum f hf]
  -- LHS: ∑ᶠ d, (∑ᶠ i, coeff d (f i)) * coeff n (g ^ d)
  -- RHS: ∑ᶠ i, coeff n (subst g (f i))
  have rhs_eq : ∀ i, coeff n (PowerSeries.subst g (f i)) =
      ∑ᶠ d, coeff d (f i) * coeff n (g ^ d) := by
    intro i
    rw [coeff_subst' ha (f i) n]
    simp only [smul_eq_mul]
  conv_rhs => rw [show (∑ᶠ i, coeff n (PowerSeries.subst g (f i))) =
      ∑ᶠ i, ∑ᶠ d, coeff d (f i) * coeff n (g ^ d) by simp_rw [rhs_eq]]
  -- RHS: ∑ᶠ i, ∑ᶠ d, coeff d (f i) * coeff n (g ^ d)
  -- Distribute the multiplication on LHS: (∑ᶠ i, aᵢ) * b = ∑ᶠ i, aᵢ * b
  have h1 : ∀ d, (∑ᶠ i, coeff d (f i)) * coeff n (g ^ d) =
      ∑ᶠ i, coeff d (f i) * coeff n (g ^ d) := by
    intro d
    rw [finsum_mul' (fun i => coeff d (f i)) (coeff n (g ^ d)) (hf d)]
  conv_lhs => rw [show (∑ᶠ d, (∑ᶠ i, coeff d (f i)) * coeff n (g ^ d)) =
      ∑ᶠ d, ∑ᶠ i, coeff d (f i) * coeff n (g ^ d) by simp_rw [h1]]
  -- Now need Fubini: ∑ᶠ d, ∑ᶠ i, ... = ∑ᶠ i, ∑ᶠ d, ...
  -- The double sum is essentially finite because:
  -- 1. For d > n, coeff n (g ^ d) = 0, so the inner sum is 0
  -- 2. For each d ≤ n, only finitely many i have coeff d (f i) ≠ 0
  -- Key observation: for d > n, coeff n (g ^ d) = 0
  have hd_finite : ∀ d > n, coeff n (g ^ d) = 0 := by
    intro d hd
    have h_order : (d : ℕ∞) ≤ (g ^ d).order := le_order_pow_of_constantCoeff_eq_zero d hg
    exact coeff_of_lt_order n (lt_of_lt_of_le (Nat.cast_lt.mpr hd) h_order)
  -- Define finite sets that cover all nonzero (d, i) pairs
  let S_d := Finset.range (n + 1)
  -- The set of i that matter
  let S_i_set : Set ι := ⋃ d ∈ S_d, {i | coeff d (f i) ≠ 0}
  have h_S_i_finite : S_i_set.Finite := by
    apply Set.Finite.biUnion (Finset.finite_toSet S_d)
    intro d _
    exact hf d
  let S_i := h_S_i_finite.toFinset
  -- Any nonzero term (d, i) has d ∈ S_d and i ∈ S_i
  have h_supp_d : ∀ d i, coeff d (f i) * coeff n (g ^ d) ≠ 0 → d ∈ S_d := by
    intro d i h
    simp only [S_d, Finset.mem_range]
    by_contra hc
    push Not at hc
    have : n < d := Nat.lt_of_succ_le hc
    rw [hd_finite d this, mul_zero] at h
    exact h rfl
  have h_supp_i : ∀ d i, coeff d (f i) * coeff n (g ^ d) ≠ 0 → i ∈ S_i := by
    intro d i h
    simp only [S_i, Set.Finite.mem_toFinset, S_i_set, Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨d, ?_, ?_⟩
    · exact h_supp_d d i h
    · intro h_zero
      rw [h_zero, zero_mul] at h
      exact h rfl
  -- LHS = ∑ᶠ d, ∑ᶠ i, coeff d (f i) * coeff n (g ^ d)
  -- = ∑ d ∈ S_d, ∑ i ∈ S_i, coeff d (f i) * coeff n (g ^ d)
  have lhs_eq : (∑ᶠ d, ∑ᶠ i, coeff d (f i) * coeff n (g ^ d)) =
      ∑ d ∈ S_d, ∑ i ∈ S_i, coeff d (f i) * coeff n (g ^ d) := by
    -- First convert outer finsum to finite sum
    have h_outer : (∑ᶠ d, ∑ᶠ i, coeff d (f i) * coeff n (g ^ d)) =
        ∑ d ∈ S_d, ∑ᶠ i, coeff d (f i) * coeff n (g ^ d) := by
      apply finsum_eq_sum_of_support_subset
      intro d hd
      simp only [Function.mem_support] at hd
      simp only [S_d, Finset.coe_range, Set.mem_Iio]
      by_contra h
      push Not at h
      have hdn : n < d := Nat.lt_of_succ_le h
      have hz : ∀ i, coeff d (f i) * coeff n (g ^ d) = 0 := fun i => by
        rw [hd_finite d hdn, mul_zero]
      simp only [finsum_eq_zero_of_forall_eq_zero hz, ne_eq, not_true_eq_false] at hd
    rw [h_outer]
    apply Finset.sum_congr rfl
    intro d hd
    -- Convert inner finsum to finite sum over S_i
    apply finsum_eq_sum_of_support_subset
    intro i hi
    simp only [Function.mem_support] at hi
    exact h_supp_i d i hi
  -- RHS = ∑ᶠ i, ∑ᶠ d, coeff d (f i) * coeff n (g ^ d)
  -- = ∑ i ∈ S_i, ∑ d ∈ S_d, coeff d (f i) * coeff n (g ^ d)
  have rhs_eq' : (∑ᶠ i, ∑ᶠ d, coeff d (f i) * coeff n (g ^ d)) =
      ∑ i ∈ S_i, ∑ d ∈ S_d, coeff d (f i) * coeff n (g ^ d) := by
    -- First convert outer finsum to finite sum
    have h_outer : (∑ᶠ i, ∑ᶠ d, coeff d (f i) * coeff n (g ^ d)) =
        ∑ i ∈ S_i, ∑ᶠ d, coeff d (f i) * coeff n (g ^ d) := by
      apply finsum_eq_sum_of_support_subset
      intro i hi
      simp only [Function.mem_support] at hi
      -- If ∑ᶠ d, ... ≠ 0, then there exists some d where the term is nonzero
      by_contra h_contra
      have hz : ∀ d, coeff d (f i) * coeff n (g ^ d) = 0 := by
        intro d
        by_cases hd : d < n + 1
        · have h_coeff_zero : coeff d (f i) = 0 := by
            by_contra h_ne
            have h_in : i ∈ S_i := by
              simp only [S_i, Set.Finite.mem_toFinset, S_i_set, Set.mem_iUnion, Set.mem_ofPred_eq]
              exact ⟨d, Finset.mem_range.mpr hd, h_ne⟩
            exact h_contra h_in
          rw [h_coeff_zero, zero_mul]
        · push Not at hd
          have hdn : n < d := Nat.lt_of_succ_le hd
          rw [hd_finite d hdn, mul_zero]
      simp only [finsum_eq_zero_of_forall_eq_zero hz, ne_eq, not_true_eq_false] at hi
    rw [h_outer]
    apply Finset.sum_congr rfl
    intro i _
    -- Convert inner finsum to finite sum over S_d
    apply finsum_eq_sum_of_support_subset
    intro d hd
    simp only [Function.mem_support] at hd
    simp only [S_d, Finset.coe_range, Set.mem_Iio]
    by_contra h
    push Not at h
    have hdn : n < d := Nat.lt_of_succ_le h
    rw [hd_finite d hdn, mul_zero] at hd
    exact hd rfl
  rw [lhs_eq, rhs_eq']
  -- Now use Finset.sum_comm to exchange the order
  exact Finset.sum_comm

/-- Substituting (x + x²) into the geometric series yields 1/(1 - x - x²).
This is related to the Fibonacci generating function.

The proof uses Proposition 7.3.4(c): (1/f₂)[g] = 1[g] / f₂[g] = 1 / f₂[g].

Note: The full proof requires showing that subst preserves inverses when
the original power series has invertible constant coefficient. -/
lemma fps_geometric_subst_fibonacci {K : Type*} [Field K] :
    PowerSeries.subst (X + X^2) (geometricSeries (K := K)) = ((1 : K⟦X⟧) - X - X^2)⁻¹ := by
  -- geometricSeries = (1 - X)⁻¹
  unfold geometricSeries
  have hg : constantCoeff (X + X^2 : K⟦X⟧) = 0 := by simp
  have ha := HasSubst.of_constantCoeff_zero' hg
  -- 1 - X has constant coefficient 1 ≠ 0
  have h1mX : constantCoeff ((1 : K⟦X⟧) - X) ≠ 0 := by
    have : constantCoeff ((1 : K⟦X⟧) - X) = 1 - 0 := by
      rw [map_sub, constantCoeff_one, constantCoeff_X]
    rw [this, sub_zero]
    exact one_ne_zero
  -- Show subst preserves the inverse
  have hsubst_inv : subst (X + X^2 : K⟦X⟧) ((1 : K⟦X⟧) - X)⁻¹ =
      (subst (X + X^2 : K⟦X⟧) ((1 : K⟦X⟧) - X))⁻¹ := by
    set f := (1 : K⟦X⟧) - X with hf_def
    set g := (X + X^2 : K⟦X⟧) with hg_def
    have hfg : constantCoeff (subst g f) ≠ 0 := by
      simp only [show constantCoeff (subst g f) =
          MvPowerSeries.constantCoeff (subst g f) from rfl]
      rw [constantCoeff_subst ha]
      rw [finsum_eq_single (fun d ↦ coeff d f • MvPowerSeries.constantCoeff (g ^ d)) 0]
      · simp [MvPowerSeries.constantCoeff_one, hf_def]
      · intro d hd
        simp only [smul_eq_mul]
        have h1 : MvPowerSeries.constantCoeff (g ^ d) =
            (MvPowerSeries.constantCoeff g) ^ d := map_pow _ _ _
        have h2 : MvPowerSeries.constantCoeff g = (0 : K) := hg
        simp only [h1, h2, zero_pow hd, mul_zero]
    have h1 : subst g (f * f⁻¹) = 1 := by
      rw [PowerSeries.mul_inv_cancel _ h1mX]
      rw [← coe_substAlgHom ha, map_one]
    have h2 : subst g (f * f⁻¹) = subst g f * subst g f⁻¹ := subst_mul ha _ _
    rw [h1] at h2
    have h3 : subst g f * subst g f⁻¹ = 1 := h2.symm
    rw [eq_inv_iff_mul_eq_one hfg, mul_comm]
    exact h3
  rw [hsubst_inv]
  congr 1
  rw [← coe_substAlgHom ha, map_sub, map_one, substAlgHom_X ha]
  ring

/-- δᵢᵢ = 1 -/
@[simp]
lemma kroneckerDelta_self {α : Type*} [DecidableEq α] (i : α) :
    kroneckerDelta (K := K) i i = 1 := by simp [kroneckerDelta]

/-- δᵢⱼ = 0 when i ≠ j -/
@[simp]
lemma kroneckerDelta_ne {α : Type*} [DecidableEq α] {i j : α} (h : i ≠ j) :
    kroneckerDelta (K := K) i j = 0 := by simp [kroneckerDelta, h]

/-- Symmetry: δᵢⱼ = δⱼᵢ -/
lemma kroneckerDelta_comm {α : Type*} [DecidableEq α] (i j : α) :
    kroneckerDelta (K := K) i j = kroneckerDelta j i := by
  simp only [kroneckerDelta]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

/-- Multiplication on the left: δᵢⱼ · a = a if i = j, else 0 -/
lemma kroneckerDelta_mul_left {α : Type*} [DecidableEq α] (i j : α) (a : K) :
    kroneckerDelta (K := K) i j * a = if i = j then a else 0 := by
  simp only [kroneckerDelta]
  split_ifs <;> ring

/-- Multiplication on the right: a · δᵢⱼ = a if i = j, else 0 -/
lemma kroneckerDelta_mul_right {α : Type*} [DecidableEq α] (i j : α) (a : K) :
    a * kroneckerDelta (K := K) i j = if i = j then a else 0 := by
  simp only [kroneckerDelta]
  split_ifs <;> ring

/-- Sum over the first index: ∑ᵢ δᵢⱼ = 1 -/
lemma sum_kroneckerDelta_left {α : Type*} [DecidableEq α] [Fintype α] (j : α) :
    ∑ i, kroneckerDelta (K := K) i j = 1 := by
  rw [Fintype.sum_eq_single j (fun i hi => kroneckerDelta_ne hi)]
  exact kroneckerDelta_self j

/-- Sum over the second index: ∑ⱼ δᵢⱼ = 1 -/
lemma sum_kroneckerDelta_right {α : Type*} [DecidableEq α] [Fintype α] (i : α) :
    ∑ j, kroneckerDelta (K := K) i j = 1 := by
  have h : ∀ j, kroneckerDelta (K := K) i j = kroneckerDelta j i := fun j => kroneckerDelta_comm i j
  simp_rw [h]
  rw [Fintype.sum_eq_single i (fun j hj => kroneckerDelta_ne hj)]
  exact kroneckerDelta_self i

/-- Contraction/selection property: ∑ᵢ δᵢⱼ · f(i) = f(j)

This is the key property that makes Kronecker delta useful:
summing over one index "selects" the value at the other index. -/
lemma sum_kroneckerDelta_mul {α : Type*} [DecidableEq α] [Fintype α] (j : α) (f : α → K) :
    ∑ i, kroneckerDelta (K := K) i j * f i = f j := by
  simp only [kroneckerDelta_mul_left]
  rw [Fintype.sum_eq_single j]
  · simp
  · intro i hi
    simp [hi]

/-- Contraction/selection property (variant): ∑ⱼ f(j) · δᵢⱼ = f(i) -/
lemma sum_mul_kroneckerDelta {α : Type*} [DecidableEq α] [Fintype α] (i : α) (f : α → K) :
    ∑ j, f j * kroneckerDelta (K := K) i j = f i := by
  simp only [kroneckerDelta_mul_right]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hj
    simp [hj.symm]

/-- Kronecker delta for natural numbers (explicit form) -/
lemma kroneckerDelta_nat_eq {n m : ℕ} :
    kroneckerDelta (K := K) n m = if n = m then 1 else 0 := rfl

/-- Kronecker delta for integers (explicit form) -/
lemma kroneckerDelta_int_eq {n m : ℤ} :
    kroneckerDelta (K := K) n m = if n = m then 1 else 0 := rfl

/-- Kronecker delta equals zero iff the indices are different -/
lemma kroneckerDelta_eq_zero_iff {α : Type*} [DecidableEq α] [Nontrivial K] {i j : α} :
    kroneckerDelta (K := K) i j = 0 ↔ i ≠ j := by
  simp [kroneckerDelta]

/-- Kronecker delta equals one iff the indices are equal (when 1 ≠ 0) -/
lemma kroneckerDelta_eq_one_iff {α : Type*} [DecidableEq α] [Nontrivial K] {i j : α} :
    kroneckerDelta (K := K) i j = 1 ↔ i = j := by
  simp [kroneckerDelta]

end AlgebraicCombinatorics
end


/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_comp_eq_subst
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f : K⟦X⟧) :
-- imply
  fps_comp f g hg = PowerSeries.subst g f := by
-- proof
  apply AlgebraicCombinatorics.fps_comp_eq_subst f g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_comp_coeff
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f : K⟦X⟧)
  (n : ℕ) :
-- imply
  coeff n (PowerSeries.subst g f) = finsum (fun d => coeff d f * coeff n (g ^ d)) := by
-- proof
  apply AlgebraicCombinatorics.fps_comp_coeff f g hg n

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_subs_wd_firstCoeffs
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (n k : ℕ)
  (hg : constantCoeff g = 0)
  (hk : k < n) :
-- imply
  coeff k (g ^ n) = 0 := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_wd_firstCoeffs g hg n k hk

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_comp_coeff_finite
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f : K⟦X⟧)
  (n : ℕ) :
-- imply
  coeff n (PowerSeries.subst g f) =
    ∑ d ∈ Finset.range (n + 1), coeff d f * coeff n (g ^ d) := by
-- proof
  apply AlgebraicCombinatorics.fps_comp_coeff_finite f g hg n

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_subs_wd_summable
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f : K⟦X⟧) :
-- imply
  HasSubst g := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_wd_summable f g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_subs_wd_constCoeff
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f : K⟦X⟧) :
-- imply
  constantCoeff (PowerSeries.subst g f) = constantCoeff f := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_wd_constCoeff f g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_fg_coeffs_zero
  [CommRing K]
-- given
  (f g : K⟦X⟧)
  (k : ℕ)
  (hg : constantCoeff g = 0)
  (hf : ∀ m < k, coeff m f = 0) :
-- imply
  ∀ m < k, coeff m (PowerSeries.subst g f) = 0 := by
-- proof
  apply AlgebraicCombinatorics.fps_fg_coeffs_zero f g hg k hf

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_subs_add
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f₁ f₂ : K⟦X⟧) :
-- imply
  PowerSeries.subst g (f₁ + f₂) = PowerSeries.subst g f₁ + PowerSeries.subst g f₂ := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_add f₁ f₂ g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_subs_mul
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f₁ f₂ : K⟦X⟧) :
-- imply
  PowerSeries.subst g (f₁ * f₂) = PowerSeries.subst g f₁ * PowerSeries.subst g f₂ := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_mul f₁ f₂ g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_subs_div
  [Field K]
-- given
  (f₂ g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (hf₂ : constantCoeff f₂ ≠ 0)
  (f₁ : K⟦X⟧) :
-- imply
  PowerSeries.subst g f₁ * (PowerSeries.subst g f₂)⁻¹ =
    PowerSeries.subst g (f₁ * f₂⁻¹) := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_div f₁ f₂ g hg hf₂

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_subs_pow
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (f : K⟦X⟧)
  (k : ℕ) :
-- imply
  PowerSeries.subst g (f ^ k) = (PowerSeries.subst g f) ^ k := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_pow f g hg k

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_subs_assoc_constCoeff
  [CommRing K]
-- given
  (g h : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (hh : constantCoeff h = 0) :
-- imply
  constantCoeff (PowerSeries.subst h g) = 0 := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_assoc_constCoeff g h hg hh

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_subs_assoc
  [CommRing K]
-- given
  (g h : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (hh : constantCoeff h = 0)
  (f : K⟦X⟧) :
-- imply
  PowerSeries.subst h (PowerSeries.subst g f) =
    PowerSeries.subst (PowerSeries.subst h g) f := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_assoc f g h hg hh

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_subs_const
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (a : K) :
-- imply
  PowerSeries.subst g (C a) = C a := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_const a g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_subs_X_left
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0) :
-- imply
  PowerSeries.subst g (X : K⟦X⟧) = g := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_X_left g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_subs_X_right
  [CommRing K]
-- given
  (g : K⟦X⟧) :
-- imply
  PowerSeries.subst X g = g := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_X_right

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_subs_sum
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0)
  (s : Finset ι)
  (f : ι → K⟦X⟧) :
-- imply
  PowerSeries.subst g (∑ i ∈ s, f i) = ∑ i ∈ s, PowerSeries.subst g (f i) := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_sum s f g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_subs_summable
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (f : ι → K⟦X⟧)
  (hg : constantCoeff g = 0)
  (hf : SummableFPS f) :
-- imply
  SummableFPS (fun i => PowerSeries.subst g (f i)) := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_summable f g hg hf

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_subs_summableFPSSum
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (f : ι → K⟦X⟧)
  (hg : constantCoeff g = 0)
  (hf : SummableFPS f) :
-- imply
  PowerSeries.subst g (summableFPSSum f hf) =
    summableFPSSum (fun i => PowerSeries.subst g (f i))
      (AlgebraicCombinatorics.fps_subs_summable f g hg hf) := by
-- proof
  apply AlgebraicCombinatorics.fps_subs_summableFPSSum f g hg hf

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_fps_geometric_subst_fibonacci
  [Field K] :
-- imply
  PowerSeries.subst (X + X ^ 2) (geometricSeries (K := K)) = ((1 : K⟦X⟧) - X - X ^ 2)⁻¹ := by
-- proof
  apply AlgebraicCombinatorics.fps_geometric_subst_fibonacci

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_kroneckerDelta_self
  [CommRing K] [DecidableEq α]
-- given
  (i : α) :
-- imply
  kroneckerDelta (K := K) i i = 1 := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_self

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_kroneckerDelta_ne
  [CommRing K] [DecidableEq α]
-- given
  {i j : α}
  (h : i ≠ j) :
-- imply
  kroneckerDelta (K := K) i j = 0 := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_ne h

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_kroneckerDelta_comm
  [CommRing K] [DecidableEq α]
-- given
  (i j : α) :
-- imply
  kroneckerDelta (K := K) i j = kroneckerDelta j i := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_comm

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_kroneckerDelta_mul_left
  [CommRing K] [DecidableEq α]
-- given
  (i j : α)
  (a : K) :
-- imply
  kroneckerDelta (K := K) i j * a = if i = j then a else 0 := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_mul_left

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_kroneckerDelta_mul_right
  [CommRing K] [DecidableEq α]
-- given
  (i j : α)
  (a : K) :
-- imply
  a * kroneckerDelta (K := K) i j = if i = j then a else 0 := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_mul_right

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_sum_kroneckerDelta_left
  [CommRing K] [DecidableEq α] [Fintype α]
-- given
  (j : α) :
-- imply
  ∑ i, kroneckerDelta (K := K) i j = 1 := by
-- proof
  apply AlgebraicCombinatorics.sum_kroneckerDelta_left

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_sum_kroneckerDelta_right
  [CommRing K] [DecidableEq α] [Fintype α]
-- given
  (i : α) :
-- imply
  ∑ j, kroneckerDelta (K := K) i j = 1 := by
-- proof
  apply AlgebraicCombinatorics.sum_kroneckerDelta_right

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_sum_kroneckerDelta_mul
  [CommRing K] [DecidableEq α] [Fintype α]
-- given
  (j : α)
  (f : α → K) :
-- imply
  ∑ i, kroneckerDelta (K := K) i j * f i = f j := by
-- proof
  apply AlgebraicCombinatorics.sum_kroneckerDelta_mul

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_sum_mul_kroneckerDelta
  [CommRing K] [DecidableEq α] [Fintype α]
-- given
  (i : α)
  (f : α → K) :
-- imply
  ∑ j, f j * kroneckerDelta (K := K) i j = f i := by
-- proof
  apply AlgebraicCombinatorics.sum_mul_kroneckerDelta

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_kroneckerDelta_nat_eq
  [CommRing K]
-- given
  (n m : ℕ) :
-- imply
  kroneckerDelta (K := K) n m = if n = m then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_nat_eq

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_kroneckerDelta_int_eq
  [CommRing K]
-- given
  (n m : ℤ) :
-- imply
  kroneckerDelta (K := K) n m = if n = m then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_int_eq

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_kroneckerDelta_eq_zero_iff
  [CommRing K] [DecidableEq α] [Nontrivial K]
-- given
  {i j : α} :
-- imply
  kroneckerDelta (K := K) i j = 0 ↔ i ≠ j := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_eq_zero_iff

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma pv_kroneckerDelta_eq_one_iff
  [CommRing K] [DecidableEq α] [Nontrivial K]
-- given
  {i j : α} :
-- imply
  kroneckerDelta (K := K) i j = 1 ↔ i = j := by
-- proof
  apply AlgebraicCombinatorics.kroneckerDelta_eq_one_iff

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma x_subst_zero
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0) :
-- imply
  PowerSeries.subst g (0 : K⟦X⟧) = 0 := by
-- proof
  apply AlgebraicCombinatorics.subst_zero g hg

/--
[Substitution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Substitution.lean)
-/
@[path]
private lemma x_subst_one
  [CommRing K]
-- given
  (g : K⟦X⟧)
  (hg : constantCoeff g = 0) :
-- imply
  PowerSeries.subst g (1 : K⟦X⟧) = 1 := by
-- proof
  apply AlgebraicCombinatorics.subst_one g hg


-- created on 2026-10-20
-- updated on 2026-10-26
