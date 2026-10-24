/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import sympy.series.formal.InfiniteProducts
import Lemma.PowerSeries.InfiniteProducts
/-!
# Exponentials and Logarithms of Formal Power Series

This file formalizes Section 7.8 (Exponentials and logarithms) from the Algebraic Combinatorics
textbook. It develops the theory of exponential and logarithm operations on formal power series
over ℚ-algebras.

## Convention

Throughout this file, `K` is assumed to be a commutative ℚ-algebra (Convention 7.8.1 in the text).
This allows division by positive integers.

## Main Definitions

* `PowerSeries.logbar`: The FPS `∑_{n≥1} (-1)^{n-1}/n · x^n`, the Mercator series for `log(1+x)`.
* `PowerSeries.expbar`: The FPS `exp - 1 = ∑_{n≥1} 1/n! · x^n`.
* `PowerSeries.PowerSeries₀`: The set of FPS with constant term 0.
* `PowerSeries.PowerSeries₁`: The set of FPS with constant term 1.
* `PowerSeries.Exp`: The map `g ↦ exp ∘ g` from `K⟦X⟧₀` to `K⟦X⟧₁`.
* `PowerSeries.Log`: The map `f ↦ logbar ∘ (f - 1)` from `K⟦X⟧₁` to `K⟦X⟧₀`.
* `PowerSeries.loder`: The logarithmic derivative `f'/f` for FPS with constant term 1.

## Main Results

* `PowerSeries.derivative_exp`: `exp' = exp` (Definition 7.8.2 / Proposition 7.8.3)
* `PowerSeries.derivative_expbar`: `expbar' = exp` (Proposition 7.8.3)
* `PowerSeries.derivative_logbar`: `logbar' = (1+x)⁻¹` (Proposition 7.8.3)
* `PowerSeries.derivative_exp_comp`: `(exp ∘ g)' = (exp ∘ g) · g'` (Proposition 7.8.3(a))
* `PowerSeries.derivative_expbar_comp`: `(expbar ∘ g)' = (exp ∘ g) · g'` (Proposition 7.8.3(a))
* `PowerSeries.derivative_logbar_comp`: `(logbar ∘ g)' = (1+g)⁻¹ · g'` (Proposition 7.8.3(b))
* `PowerSeries.expbar_comp_logbar`: `expbar ∘ logbar = x` (Theorem 7.8.5)
* `PowerSeries.logbar_comp_expbar`: `logbar ∘ expbar = x` (Theorem 7.8.5)
* `PowerSeries.Log_Exp` and `PowerSeries.Exp_Log`: `Exp` and `Log` are mutually inverse (Lemma 7.8.8)
* `PowerSeries.Exp_add`: `Exp(f + g) = Exp(f) · Exp(g)` (Lemma 7.8.9)
* `PowerSeries.Log_mul`: `Log(fg) = Log(f) + Log(g)` (Lemma 7.8.9)
* `PowerSeries.Exp_Log_groupIso`: `Exp` is a group isomorphism (Theorem 7.8.11)
* `PowerSeries.loder_mul`: `loder(fg) = loder(f) + loder(g)` (Proposition 7.8.14)
* `PowerSeries.loder_inv`: `loder(f⁻¹) = -loder(f)` (Corollary 7.8.16)
* `PowerSeries.Log_tprod`: `Log(∏ fᵢ) = ∑ Log(fᵢ)` for infinite products (Proposition prop.fps.Exp-Log-infprod)
* `PowerSeries.Exp_sum`: `Exp(∑ gᵢ) = ∏ Exp(gᵢ)` for infinite sums (Proposition prop.fps.Exp-Log-infsum)

## References

* [Darij Grinberg, *Algebraic Combinatorics*, Section 7.8]
* [Grinberg-Reiner, *logexp*, Lemma 0.4 and Theorem 0.1]

## Tags

power series, exponential, logarithm, formal power series
-/


namespace PowerSeries

open Nat Finset

variable (K : Type*) [CommRing K] [Algebra ℚ K]
/-! ## Section 7.8.1: Definitions -/


/-- The logarithm series `logbar = ∑_{n≥1} (-1)^{n-1}/n · x^n`, which is the Mercator series
for `log(1+x)`. This is `\overline{\log}` in Definition 7.8.2 (def.fps.exp-log). -/
noncomputable def logbar : K⟦X⟧ :=
  mk fun n => if n = 0 then 0 else algebraMap ℚ K ((-1 : ℚ) ^ (n - 1) / n)

/-- The shifted exponential series `expbar = exp - 1 = ∑_{n≥1} 1/n! · x^n`.
This is `\overline{\exp}` in Definition 7.8.2 (def.fps.exp-log). -/
noncomputable def expbar : K⟦X⟧ := exp K - 1

variable {K}
/-! ### Basic coefficient lemmas -/
/-! ### Explicit coefficient values for Definition 7.8.2 (def.fps.exp-log)

These lemmas verify that our definitions match the textbook formulas:
- `exp = ∑_{n≥0} (1/n!) x^n`
- `logbar = ∑_{n≥1} ((-1)^{n-1}/n) x^n`
- `expbar = ∑_{n≥1} (1/n!) x^n`
-/
/-! ## Section 7.8.2: The exponential and logarithm are inverse -/


@[simp]
theorem coeff_logbar (n : ℕ) :
    coeff n (logbar K) = if n = 0 then 0 else algebraMap ℚ K ((-1 : ℚ) ^ (n - 1) / n) :=
  coeff_mk _ _

@[simp]
theorem constantCoeff_logbar : constantCoeff (logbar K) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_logbar]
  simp
variable (K) in
/-- The series `(1+x)⁻¹ = ∑_{n≥0} (-1)^n x^n`. -/
noncomputable def invOnePlusX : K⟦X⟧ := mk fun n => algebraMap ℚ K ((-1 : ℚ) ^ n)

section FieldLemmas

variable {K : Type*} [Field K] [Algebra ℚ K]

-- Instances needed for derivative.ext (Field K + Algebra ℚ K gives CharZero and IsAddTorsionFree)
private instance charZero_of_algebraRat : CharZero K := algebraRat.charZero K
private instance isAddTorsionFree_of_field : IsAddTorsionFree K :=
  IsAddTorsionFree.of_isCancelMulZero_charZero

end FieldLemmas

omit [Algebra ℚ K] in
/-- The constant term of a composition `f ∘ g` where `g` has constant term 0.
This is Lemma 7.8.4 (lem.fps.compos-cst-term-0).

Note: Mathlib has `PowerSeries.constantCoeff_subst` which requires `HasSubst`. -/
theorem constantCoeff_subst_eq_apply {f g : K⟦X⟧} (hg : constantCoeff g = 0) :
    constantCoeff (f.subst g) = constantCoeff f := by
  -- We use the Mathlib lemma constantCoeff_subst which expresses the result as a finsum
  show MvPowerSeries.constantCoeff (f.subst g) = constantCoeff f
  rw [constantCoeff_subst (HasSubst.of_constantCoeff_zero' hg)]
  -- The finsum is: ∑ᶠ d, coeff d f • constantCoeff (g ^ d)
  -- Only d = 0 contributes since constantCoeff (g^d) = 0 for d ≥ 1
  have hd : ∀ d : ℕ, d ≠ 0 → MvPowerSeries.constantCoeff (g ^ d) = 0 := fun d hd => by
    have : MvPowerSeries.constantCoeff (R := K) (σ := Unit) g = constantCoeff g := rfl
    rw [map_pow, this, hg]
    exact zero_pow hd
  rw [finsum_eq_single (fun d => coeff d f • MvPowerSeries.constantCoeff (g ^ d)) 0]
  · simp
  · intro d hd'
    simp [hd d hd']
/-! ## Section 7.8.3: The exponential and logarithm of an FPS -/


section PowerSeriesSets

variable {R : Type*} [CommRing R]

/-- `R⟦X⟧₀` is the set of FPS with constant term 0.
This is Definition 7.8.6(a) (def.fps.Exp-Log-maps). -/
def PowerSeries₀ : Set R⟦X⟧ := {f | constantCoeff f = 0}

/-- `R⟦X⟧₁` is the set of FPS with constant term 1.
This is Definition 7.8.6(b) (def.fps.Exp-Log-maps). -/
def PowerSeries₁ : Set R⟦X⟧ := {f | constantCoeff f = 1}

theorem mem_PowerSeries₀_iff {f : R⟦X⟧} : f ∈ PowerSeries₀ ↔ constantCoeff f = 0 := Iff.rfl

theorem mem_PowerSeries₁_iff {f : R⟦X⟧} : f ∈ PowerSeries₁ ↔ constantCoeff f = 1 := Iff.rfl

/-- `R⟦X⟧₀` is closed under addition and subtraction and contains 0.
This is Proposition 7.8.10(a) (prop.fps.Exp-Log-groups). -/
theorem PowerSeries₀.zero_mem : (0 : R⟦X⟧) ∈ PowerSeries₀ := by simp [mem_PowerSeries₀_iff]

theorem PowerSeries₀.add_mem {f g : R⟦X⟧} (hf : f ∈ PowerSeries₀) (hg : g ∈ PowerSeries₀) :
    f + g ∈ PowerSeries₀ := by
  rw [mem_PowerSeries₀_iff, map_add]
  rw [mem_PowerSeries₀_iff] at hf hg
  rw [hf, hg, add_zero]

theorem PowerSeries₀.neg_mem {f : R⟦X⟧} (hf : f ∈ PowerSeries₀) : -f ∈ PowerSeries₀ := by
  rw [mem_PowerSeries₀_iff, map_neg]
  rw [mem_PowerSeries₀_iff] at hf
  rw [hf, neg_zero]

/-- `R⟦X⟧₁` is closed under multiplication and division and contains 1.
This is Proposition 7.8.10(b) (prop.fps.Exp-Log-groups). -/
theorem PowerSeries₁.one_mem : (1 : R⟦X⟧) ∈ PowerSeries₁ := by simp [mem_PowerSeries₁_iff]

theorem PowerSeries₁.mul_mem {f g : R⟦X⟧} (hf : f ∈ PowerSeries₁) (hg : g ∈ PowerSeries₁) :
    f * g ∈ PowerSeries₁ := by
  rw [mem_PowerSeries₁_iff, map_mul]
  rw [mem_PowerSeries₁_iff] at hf hg
  rw [hf, hg, one_mul]

/-- If `f` has constant term 1, then `f - 1` has constant term 0.
This is Lemma 7.8.7(d) (lem.fps.Exp-Log-maps-wd). -/
theorem sub_one_mem_PowerSeries₀ {f : R⟦X⟧} (hf : f ∈ PowerSeries₁) :
    f - 1 ∈ PowerSeries₀ := by
  rw [mem_PowerSeries₀_iff, map_sub, map_one, mem_PowerSeries₁_iff.mp hf, sub_self]

/-- `R⟦X⟧₀` forms an additive subgroup.
This is Proposition 7.8.10(a) (prop.fps.Exp-Log-groups). -/
def PowerSeries₀.addSubgroup : AddSubgroup R⟦X⟧ where
  carrier := PowerSeries₀
  zero_mem' := PowerSeries₀.zero_mem
  add_mem' := PowerSeries₀.add_mem
  neg_mem' := PowerSeries₀.neg_mem

end PowerSeriesSets

section PowerSeriesSetsField

variable {R : Type*} [Field R]

/-- `R⟦X⟧₁` forms a multiplicative subgroup of units.
This is Proposition 7.8.10(b) (prop.fps.Exp-Log-groups). -/
def PowerSeries₁.subgroup : Subgroup (R⟦X⟧)ˣ where
  carrier := {u | (u : R⟦X⟧) ∈ PowerSeries₁}
  one_mem' := PowerSeries₁.one_mem
  mul_mem' := fun hf hg => PowerSeries₁.mul_mem hf hg
  inv_mem' := fun {u} hf => by
    simp only [Set.mem_ofPred_eq] at hf ⊢
    rw [mem_PowerSeries₁_iff] at hf ⊢
    -- For a unit u, we have u * u⁻¹ = 1, so constantCoeff(u) * constantCoeff(u⁻¹) = 1
    have h : (u : R⟦X⟧) * u.inv = 1 := Units.mul_inv u
    have hcc : constantCoeff ((u : R⟦X⟧) * u.inv) = 1 := by rw [h]; simp
    rw [map_mul] at hcc
    rw [hf, one_mul] at hcc
    exact hcc

end PowerSeriesSetsField

section ExpLogMaps

variable (K : Type*) [CommRing K] [Algebra ℚ K]

theorem exp_mem_PowerSeries₁ : exp K ∈ PowerSeries₁ := constantCoeff_exp

theorem logbar_mem_PowerSeries₀ : logbar K ∈ PowerSeries₀ := constantCoeff_logbar

variable {K}

omit [Algebra ℚ K] in
/-- Composition of two FPS with constant term 0 has constant term 0.
This is Lemma 7.8.7(a) (lem.fps.Exp-Log-maps-wd). -/
theorem PowerSeries₀.subst_mem {f g : K⟦X⟧} (hf : f ∈ PowerSeries₀) (hg : g ∈ PowerSeries₀) :
    f.subst g ∈ PowerSeries₀ := by
  rw [mem_PowerSeries₀_iff] at hf hg ⊢
  rw [constantCoeff_subst_eq_apply hg, hf]

omit [Algebra ℚ K] in
/-- Composition of an FPS with constant term 1 and one with constant term 0 has constant term 1.
This is Lemma 7.8.7(b) (lem.fps.Exp-Log-maps-wd). -/
theorem PowerSeries₁.subst_mem {f g : K⟦X⟧} (hf : f ∈ PowerSeries₁) (hg : g ∈ PowerSeries₀) :
    f.subst g ∈ PowerSeries₁ := by
  rw [mem_PowerSeries₁_iff] at hf ⊢
  rw [mem_PowerSeries₀_iff] at hg
  rw [constantCoeff_subst_eq_apply hg, hf]

/-- `exp ∘ g` has constant term 1 when `g` has constant term 0.
This is Lemma 7.8.7(c) (lem.fps.Exp-Log-maps-wd). -/
theorem exp_subst_mem_PowerSeries₁ {g : K⟦X⟧} (hg : g ∈ PowerSeries₀) :
    (exp K).subst g ∈ PowerSeries₁ :=
  PowerSeries₁.subst_mem (exp_mem_PowerSeries₁ K) hg

theorem logbar_subst_sub_one_mem_PowerSeries₀ {f : K⟦X⟧} (hf : f ∈ PowerSeries₁) :
    (logbar K).subst (f - 1) ∈ PowerSeries₀ :=
  PowerSeries₀.subst_mem (logbar_mem_PowerSeries₀ K) (sub_one_mem_PowerSeries₀ hf)

/-- The exponential map `Exp : K⟦X⟧₀ → K⟦X⟧₁` defined by `g ↦ exp ∘ g`.
This is Definition 7.8.6(c) (def.fps.Exp-Log-maps). -/
noncomputable def Exp (g : PowerSeries₀ (R := K)) : PowerSeries₁ (R := K) :=
  ⟨(exp K).subst g.val, exp_subst_mem_PowerSeries₁ g.property⟩

/-- The logarithm map `Log : K⟦X⟧₁ → K⟦X⟧₀` defined by `f ↦ logbar ∘ (f - 1)`.
This is Definition 7.8.6(c) (def.fps.Exp-Log-maps). -/
noncomputable def Log (f : PowerSeries₁ (R := K)) : PowerSeries₀ (R := K) :=
  ⟨(logbar K).subst (f.val - 1), logbar_subst_sub_one_mem_PowerSeries₀ f.property⟩
/-! ## Section 7.8.4: Addition to multiplication -/

end ExpLogMaps
/-! ## Section 7.8.5: The logarithmic derivative -/


section LogarithmicDerivative

variable {R : Type*} [Field R]

/-- **Definition 7.8.12 (def.fps.loder.1)**: The logarithmic derivative.

For any FPS `f ∈ R⟦X⟧₁` (i.e., with constant term 1), we define the *logarithmic derivative*
`loder f ∈ R⟦X⟧` to be the FPS `f'/f`.

This is well-defined since `f` is invertible when `constantCoeff f = 1`
(see `isUnit_of_constantCoeff_eq_one`).

**Important**: This definition does NOT require `R` to be a ℚ-algebra. The definition makes
sense over any field. The name "logarithmic derivative" comes from Proposition 7.8.13
(`loder_eq_derivative_Log`), which shows that over ℚ-algebras, `loder f = (Log f)'`.

## Properties

* `loder_one`: `loder 1 = 0`
* `loder_mul`: `loder(fg) = loder f + loder g` (Proposition 7.8.14)
* `loder_inv`: `loder(f⁻¹) = -loder f` (Corollary 7.8.16)
* `loder_prod`: `loder(∏ fᵢ) = ∑ loder fᵢ` (Corollary 7.8.15)
-/
noncomputable def loder (f : R⟦X⟧) : R⟦X⟧ := d⁄dX f * f⁻¹
/-! ### Well-definedness of loder (def.fps.loder.1)

The logarithmic derivative is well-defined for FPS with constant term 1 because such FPS
are invertible. The following lemmas establish this. -/

end LogarithmicDerivative
/-! ## Section 7.10.2: Exp and Log for Infinite Products

The Exp and Log maps convert between infinite sums and products.
These results require K to be a ℚ-algebra for the formal exp and log to be defined.

Propositions prop.fps.Exp-Log-infsum and prop.fps.Exp-Log-infprod state:
- `Exp(∑_{i ∈ I} f_i) = ∏_{i ∈ I} Exp(f_i)` for summable families in `K⟦X⟧_0`
- `Log(∏_{i ∈ I} f_i) = ∑_{i ∈ I} Log(f_i)` for multipliable families in `K⟦X⟧_1`
-/


section ExpLogInfinite

variable {K : Type*} [CommRing K] [Algebra ℚ K]
variable {I : Type*}
/-! ### Summable families in K⟦X⟧₀ -/


/-- A family of FPS in `K⟦X⟧₀` is summable if for each coefficient index n,
only finitely many family members have nonzero n-th coefficient.

This is the notion of summability appropriate for `K⟦X⟧₀`. -/
def SummableFPS₀ (f : I → PowerSeries₀ (R := K)) : Prop :=
  ∀ n : ℕ, {i : I | (f i).val.coeff n ≠ 0}.Finite

/-- The coefficient-wise sum of a summable family in `K⟦X⟧₀`.

**Important:** This is defined coefficient-wise using `mk`, NOT using `finsum` on the entire
power series. The reason is that `finsum` returns 0 when the support is infinite, but
`SummableFPS₀` only guarantees finite support for each coefficient, not for the entire family.

For each coefficient n, only finitely many terms contribute (by `SummableFPS₀`), so the
finsum `∑ᶠ i, coeff n (f i).val` is well-defined and equals a finite sum. -/
noncomputable def summableFPS₀Sum (f : I → PowerSeries₀ (R := K)) (_hf : SummableFPS₀ f) :
    PowerSeries₀ (R := K) :=
  ⟨mk fun n => ∑ᶠ i, coeff n (f i).val, by
    rw [mem_PowerSeries₀_iff, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    rw [coeff_zero_eq_constantCoeff_apply]
    exact (f i).property⟩
/-! ### Multipliable families in K⟦X⟧₁ -/


/-- A family of FPS in `K⟦X⟧₁` is multipliable if for each coefficient index n,
the n-th coefficient of the product is finitely determined.

This is the notion of multipliability appropriate for `K⟦X⟧₁`. -/
def MultipliableFPS₁ (f : I → PowerSeries₁ (R := K)) : Prop :=
  PowerSeries.Multipliable (fun i => (f i).val)

omit [Algebra ℚ K] in
/-- For a multipliable family in `K⟦X⟧₁`, the product is also in `K⟦X⟧₁`. -/
theorem MultipliableFPS₁.prod_mem (f : I → PowerSeries₁ (R := K)) (hf : MultipliableFPS₁ f) :
    PowerSeries.tprod (fun i => (f i).val) hf ∈ PowerSeries₁ := by
  rw [mem_PowerSeries₁_iff]
  -- The constant coefficient of an infinite product of FPS with constant term 1 is 1
  -- This follows from the fact that ∅ determines the constant coefficient
  have h0 : PowerSeries.DeterminesCoeffInProd (fun i => (f i).val) ∅ 0 := by
    intro J _hJ
    simp only [Finset.prod_empty]
    -- Need to show coeff 0 (∏ i ∈ J, (f i).val) = coeff 0 1 = 1
    rw [coeff_zero_eq_constantCoeff, map_prod, map_one]
    have h : ∀ i ∈ J, constantCoeff (f i).val = 1 := fun i _ => (f i).property
    rw [Finset.prod_eq_one h]
  rw [← coeff_zero_eq_constantCoeff_apply]
  have : (coeff 0) (∏ i ∈ (∅ : Finset I), (f i).val) = 1 := by simp
  rw [PowerSeries.tprod_coeff hf h0, this]

/-- The product of a multipliable family in `K⟦X⟧₁` as an element of `K⟦X⟧₁`. -/
noncomputable def multipliableFPS₁Prod (f : I → PowerSeries₁ (R := K)) (hf : MultipliableFPS₁ f) :
    PowerSeries₁ (R := K) :=
  ⟨PowerSeries.tprod (fun i => (f i).val) hf, MultipliableFPS₁.prod_mem f hf⟩
/-! ### The main theorem: Log converts products to sums -/

end ExpLogInfinite

end PowerSeries
