/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.RingTheory.PowerSeries.InfiniteProducts
import Lemma.PowerSeries.InfiniteProducts
import Def.RingTheory.PowerSeries.ExpLog.Part4
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

variable {K}

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

end ExpLogMaps
end PowerSeries
