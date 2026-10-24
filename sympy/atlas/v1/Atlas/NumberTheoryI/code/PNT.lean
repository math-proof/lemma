/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PNT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.RiemannZeta
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Lem168
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Lem168
open Chebyshev Asymptotics Filter Topology MeasureTheory Finset
open Nat (primeCounting)
open Real (log exp)

namespace Chapter16

noncomputable def laplace_transform (h : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), (Complex.exp (-s * ↑t) : ℂ) * ↑(h t)

noncomputable def Phi (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (Real.log ↑(↑p : ℕ) : ℂ) * (↑(↑p : ℕ) : ℂ) ^ (-s)

noncomputable def PhiCorrection (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (Real.log ↑(↑p : ℕ) : ℂ) /
    ((↑(↑p : ℕ) : ℂ) ^ s * ((↑(↑p : ℕ) : ℂ) ^ s - 1))

noncomputable def G₀ : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * riemannZeta s) 1 1

noncomputable def F₀ : ℂ → ℂ := fun z => (z - 1) * G₀ z

noncomputable def boundedProj (z : ℂ) (C : ℝ) : ℂ :=
  if ‖z‖ ≤ C then z else ((C : ℂ) / (‖z‖ : ℂ)) * z

noncomputable def right_semicircle_integrand
    (g : ℂ → ℂ) (f : ℝ → ℝ) (r : ℝ) (τ u : ℝ) : ℂ :=
  let R : ℂ := (r : ℂ)
  let s : ℂ := R * Complex.exp (Complex.I * ↑u)
  boundedProj
    ((g s - ∫ t in (0:ℝ)..τ, (Complex.exp (-s * ↑t) : ℂ) * ↑(f t)) *
      Complex.exp (s * ↑τ) * (s⁻¹ + s / R ^ 2) * (R * Complex.I * Complex.exp (Complex.I * ↑u)))
    (2 / r)

noncomputable def newman_cif_I_right
    (f : ℝ → ℝ) (M : ℝ) (hM : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M)
    (g : ℂ → ℂ) (hg_holo : DifferentiableOn ℂ g {s : ℂ | 0 ≤ s.re})
    (hg_laplace : ∀ s : ℂ, 0 < s.re → g s = laplace_transform f s)
    (r : ℝ) (hr : 0 < r) : ℝ → ℂ :=
  fun τ =>
    (1 / (2 * ↑Real.pi * Complex.I)) *
      ∫ u in (-(Real.pi/2))..(Real.pi/2),
        right_semicircle_integrand g f r τ u

noncomputable def left_semicircle_integrand
    (g : ℂ → ℂ) (f : ℝ → ℝ) (r : ℝ) (τ u : ℝ) : ℂ :=
  let R : ℂ := (r : ℂ)
  let s : ℂ := R * Complex.exp (Complex.I * ↑u)
  boundedProj
    ((g s - ∫ t in (0:ℝ)..τ, (Complex.exp (-s * ↑t) : ℂ) * ↑(f t)) *
      Complex.exp (s * ↑τ) * (s⁻¹ + s / R ^ 2) * (R * Complex.I * Complex.exp (Complex.I * ↑u)))
    (2 / r)

noncomputable def newman_cif_I_left
    (f : ℝ → ℝ) (M : ℝ) (hM : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M)
    (g : ℂ → ℂ) (hg_holo : DifferentiableOn ℂ g {s : ℂ | 0 ≤ s.re})
    (hg_laplace : ∀ s : ℂ, 0 < s.re → g s = laplace_transform f s)
    (r : ℝ) (hr : 0 < r) : ℝ → ℂ :=
  fun τ =>
    (1 / (2 * ↑Real.pi * Complex.I)) *
      ∫ u in (Real.pi/2)..(3*Real.pi/2),
        left_semicircle_integrand g f r τ u

noncomputable def H (t : ℝ) : ℝ := θ (exp t) * exp (-t) - 1
