-- Author: @toskua, Avocado
-- Provenance: Adam Kiezun authored the original formalization
-- (commit 8a13ba393c1d23f85b900081c600941a4bdd56dc); @toskua, Avocado
-- authored only the Convexity.StdSimplex representation migration.

import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Tactic.Module
import Mathlib.Topology.Bases
import Def.Analysis.Convex.Straszewicz.Part2
/-!
# Straszewicz's theorem on exposed points

Every extreme point of a compact convex set in a finite-dimensional real
normed space lies in the closure of its exposed points.

Primary source: S. Straszewicz, "Über exponierte Punkte abgeschlossener
Punktmengen", Fundamenta Mathematicae 24 (1935), 139–143,
DOI 10.4064/FM-24-1-139-143.
-/


namespace Convex.Straszewicz

open Set Metric Filter TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable {h : StrongDual ℝ E → ℝ} {x : StrongDual ℝ E}

omit [FiniteDimensional ℝ E] in
/-- Restriction of a convex function to a line is convex. -/
theorem convexOn_line (hconv : ConvexOn ℝ univ h) (v : StrongDual ℝ E) :
    ConvexOn ℝ univ (fun s : ℝ => h (x + s • v)) := by
  refine ⟨convex_univ, fun s _ u _ a b ha hb hab => ?_⟩
  have key : x + (a * s + b * u) • v = a • (x + s • v) + b • (x + u • v) := by
    have e1 : (a * s + b * u) • v = a • (s • v) + b • (u • v) := by
      rw [add_smul, mul_smul, mul_smul]
    have e2 : a • x + b • x = x := by rw [← add_smul, hab, one_smul]
    calc x + (a * s + b * u) • v
        = (a • x + b • x) + (a • (s • v) + b • (u • v)) := by rw [e1, e2]
      _ = a • (x + s • v) + b • (x + u • v) := by
          rw [smul_add, smul_add]
          abel
  simp only [smul_eq_mul] at key ⊢
  rw [key]
  exact hconv.2 (mem_univ _) (mem_univ _) ha hb hab

omit [FiniteDimensional ℝ E] in
/-- Difference quotients are bounded below (slope comparison on the line). -/
theorem dirQuot_bddBelow (hconv : ConvexOn ℝ univ h) (v : StrongDual ℝ E) :
    BddBelow (dirQuot h x v) := by
  refine ⟨h x - h (x - v), fun z hz => ?_⟩
  obtain ⟨t, ht, rfl⟩ := hz
  change h x - h (x - v) ≤ (h (x + t • v) - h x) / t
  have hψ := convexOn_line (x := x) hconv v
  have hsl := ConvexOn.slope_mono_adjacent hψ (mem_univ (-1)) (mem_univ t)
    (by norm_num : (-1 : ℝ) < 0) ht
  have e0' : h (x + (0 : ℝ) • v) = h x := by simp
  have em1 : h (x + (-1 : ℝ) • v) = h (x - v) := by
    rw [neg_one_smul ℝ v, sub_eq_add_neg]
  have h1 : h x - h (x - v)
      = (h (x + (0 : ℝ) • v) - h (x + (-1 : ℝ) • v)) / ((0 : ℝ) - -1) := by
    rw [e0', em1]
    norm_num
  have h2 : (h (x + t • v) - h x) / t
      = (h (x + t • v) - h (x + (0 : ℝ) • v)) / (t - 0) := by
    rw [e0']
    norm_num
  rw [h1, h2]
  exact hsl

omit [FiniteDimensional ℝ E] in
theorem dirQuot_nonempty (v : StrongDual ℝ E) : (dirQuot h x v).Nonempty :=
  Set.image_nonempty.mpr nonempty_Ioi

omit [FiniteDimensional ℝ E] in
theorem dirDeriv_le_quot (hconv : ConvexOn ℝ univ h) (v : StrongDual ℝ E)
    {t : ℝ} (ht : 0 < t) : dirDeriv h x v ≤ (h (x + t • v) - h x) / t :=
  csInf_le (dirQuot_bddBelow hconv v) ⟨t, ht, rfl⟩

omit [FiniteDimensional ℝ E] in
/-- Subadditivity of the directional derivative (midpoint rescaling trick). -/
theorem dirDeriv_subadd (hconv : ConvexOn ℝ univ h) (v w : StrongDual ℝ E) :
    dirDeriv h x (v + w) ≤ dirDeriv h x v + dirDeriv h x w := by
  have key : ∀ s₁ s₂ : ℝ, 0 < s₁ → 0 < s₂ → dirDeriv h x (v + w)
      ≤ (h (x + s₁ • v) - h x) / s₁ + ((h (x + s₂ • w) - h x) / s₂) := by
    intro s₁ s₂ hs₁ hs₂
    set t := s₁ * s₂ / (s₁ + s₂) with ht
    have htpos : 0 < t := by
      rw [ht]
      positivity
    have hs₁' : s₁ ≠ 0 := ne_of_gt hs₁
    have hs₂' : s₂ ≠ 0 := ne_of_gt hs₂
    have hsum' : s₁ + s₂ ≠ 0 := ne_of_gt (add_pos hs₁ hs₂)
    have hlam : t / s₁ + t / s₂ = 1 := by
      rw [ht]
      field_simp
      ring
    have c1 : (t / s₁) * s₁ = t := div_mul_cancel₀ _ hs₁'
    have c2 : (t / s₂) * s₂ = t := div_mul_cancel₀ _ hs₂'
    have hdecomp : x + t • (v + w)
        = (t / s₁) • (x + s₁ • v) + (t / s₂) • (x + s₂ • w) := by
      have r1 : (t / s₁) • (s₁ • v) = t • v := by rw [← mul_smul, c1]
      have r2 : (t / s₂) • (s₂ • w) = t • w := by rw [← mul_smul, c2]
      have rx : (t / s₁) • x + (t / s₂) • x = x := by
        rw [← add_smul, hlam, one_smul]
      calc x + t • (v + w) = x + (t • v + t • w) := by rw [smul_add]
        _ = ((t / s₁) • x + (t / s₂) • x) + (t • v + t • w) := by rw [rx]
        _ = (t / s₁) • (x + s₁ • v) + (t / s₂) • (x + s₂ • w) := by
            rw [smul_add, smul_add, r1, r2]
            abel
    have hcvx := hconv.2 (mem_univ (x + s₁ • v)) (mem_univ (x + s₂ • w))
      (div_nonneg htpos.le hs₁.le) (div_nonneg htpos.le hs₂.le) hlam
    rw [← hdecomp] at hcvx
    have hQt : dirDeriv h x (v + w) ≤ (h (x + t • (v + w)) - h x) / t :=
      dirDeriv_le_quot hconv _ htpos
    have alg : ((t / s₁) * h (x + s₁ • v) + (t / s₂) * h (x + s₂ • w) - h x) / t
        = (h (x + s₁ • v) - h x) / s₁ + ((h (x + s₂ • w) - h x) / s₂) := by
      have ht' : t ≠ 0 := ne_of_gt htpos
      rw [ht]
      field_simp
      ring
    calc dirDeriv h x (v + w)
        ≤ (h (x + t • (v + w)) - h x) / t := hQt
      _ ≤ ((t / s₁) * h (x + s₁ • v) + (t / s₂) * h (x + s₂ • w) - h x) / t := by
          rw [div_le_div_iff_of_pos_right htpos]
          have hcvx' := hcvx
          simp only [smul_eq_mul] at hcvx'
          linarith
      _ = _ := alg
  have step1 : ∀ s₂ : ℝ, 0 < s₂ → dirDeriv h x (v + w)
      ≤ dirDeriv h x v + (h (x + s₂ • w) - h x) / s₂ := by
    intro s₂ hs₂
    have hle : dirDeriv h x (v + w) - (h (x + s₂ • w) - h x) / s₂
        ≤ dirDeriv h x v := by
      apply le_csInf (dirQuot_nonempty (h := h) (x := x) v)
      intro b hb
      obtain ⟨s₁, hs₁, rfl⟩ := hb
      change dirDeriv h x (v + w) - (h (x + s₂ • w) - h x) / s₂
        ≤ (h (x + s₁ • v) - h x) / s₁
      have := key s₁ s₂ hs₁ hs₂
      linarith
    linarith
  have hle : dirDeriv h x (v + w) - dirDeriv h x v ≤ dirDeriv h x w := by
    apply le_csInf (dirQuot_nonempty (h := h) (x := x) w)
    intro b hb
    obtain ⟨s₂, hs₂, rfl⟩ := hb
    change dirDeriv h x (v + w) - dirDeriv h x v ≤ (h (x + s₂ • w) - h x) / s₂
    have := step1 s₂ hs₂
    linarith
  linarith

omit [FiniteDimensional ℝ E] in
/-- The directional derivative in direction zero vanishes. -/
theorem dirDeriv_zero : dirDeriv h x 0 = 0 := by
  have hset : dirQuot h x 0 = {0} := by
    ext z
    simp only [dirQuot, Set.mem_image, Set.mem_Ioi, Set.mem_singleton_iff]
    constructor
    · rintro ⟨t, ht, rfl⟩
      simp [smul_zero, add_zero, sub_self]
    · intro hz
      refine ⟨1, one_pos, ?_⟩
      simp [hz, smul_zero, add_zero, sub_self]
  have hle : sInf ({0} : Set ℝ) ≤ 0 :=
    csInf_le ⟨0, fun b hb => by rw [Set.mem_singleton_iff.mp hb]⟩
      ((Set.mem_singleton_iff).mpr rfl)
  have hge : (0 : ℝ) ≤ sInf ({0} : Set ℝ) :=
    le_csInf ⟨0, (Set.mem_singleton_iff).mpr rfl⟩
      (fun b hb => by rw [Set.mem_singleton_iff.mp hb])
  rw [dirDeriv, hset]
  exact le_antisymm hle hge

omit [FiniteDimensional ℝ E] in
/-- The two opposite directional derivatives sum to something nonnegative. -/
theorem dirDeriv_add_neg_nonneg (hconv : ConvexOn ℝ univ h) (v : StrongDual ℝ E) :
    0 ≤ dirDeriv h x v + dirDeriv h x (-v) := by
  have hsub := dirDeriv_subadd (x := x) hconv v (-v)
  have h0 := dirDeriv_zero (h := h) (x := x)
  rw [add_neg_cancel] at hsub
  rw [h0] at hsub
  exact hsub

end Convex.Straszewicz
