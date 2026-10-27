/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.RingTheory.PowerSeries.InfiniteProducts
import Lemma.PowerSeries.InfiniteProducts
import Def.RingTheory.PowerSeries.ExpLog.Part3
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

section PowerSeriesSets

variable {R : Type*} [CommRing R]

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

end PowerSeriesSets
end PowerSeries
