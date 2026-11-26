import Def.LinearAlgebra.Matrix.Rotary
import Initialize.Tactic.Attr.Basic
import Lemma.Real.Sum_IteAnd.eq.Sum_IteAnd
import Mathlib
open Fin Real
open scoped Matrix


private lemma rotaryOn_neg
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (θ : Fin d → ℝ) :
-- imply
  Matrix.rotaryOn u v (-θ) = (Matrix.rotaryOn u v θ)ᵀ := by
-- proof
  ext i j
  have hL :
    Matrix.rotaryOn u v (-θ) i j =
      (∑ t : Fin d, if i = u t ∧ j = u t then Real.cos (θ t) else 0) +
      (∑ t : Fin d, if i = u t ∧ j = v t then Real.sin (θ t) else 0) +
      (∑ t : Fin d, if i = v t ∧ j = u t then -Real.sin (θ t) else 0) +
      (∑ t : Fin d, if i = v t ∧ j = v t then Real.cos (θ t) else 0) := by
    simp only [Matrix.rotaryOn, Matrix.of_apply, Pi.neg_apply, Finset.sum_add_distrib, Real.cos_neg,
      Real.sin_neg, neg_neg]
  have hR :
    (Matrix.rotaryOn u v θ)ᵀ i j =
      (∑ t : Fin d, if j = u t ∧ i = u t then Real.cos (θ t) else 0) +
      (∑ t : Fin d, if j = u t ∧ i = v t then -Real.sin (θ t) else 0) +
      (∑ t : Fin d, if j = v t ∧ i = u t then Real.sin (θ t) else 0) +
      (∑ t : Fin d, if j = v t ∧ i = v t then Real.cos (θ t) else 0) := by
    simp only [Matrix.transpose_apply, Matrix.rotaryOn, Matrix.of_apply, Finset.sum_add_distrib]
  rw [hL, hR]
  rw [Sum_IteAnd.eq.Sum_IteAnd (p := fun t => i = u t) (q := fun t => j = u t) (f := fun t => Real.cos (θ t))]
  rw [Sum_IteAnd.eq.Sum_IteAnd (p := fun t => i = u t) (q := fun t => j = v t) (f := fun t => Real.sin (θ t))]
  rw [Sum_IteAnd.eq.Sum_IteAnd (p := fun t => i = v t) (q := fun t => j = u t) (f := fun t => -Real.sin (θ t))]
  rw [Sum_IteAnd.eq.Sum_IteAnd (p := fun t => i = v t) (q := fun t => j = v t) (f := fun t => Real.cos (θ t))]
  ring

/-- Negating the angles transposes the interleaved rotary matrix: \(R(-\theta) = R(\theta)^{\mathsf{T}}\). -/
@[path]
private lemma main
  {d : ℕ}
-- given
  (φ : Fin d → ℝ) :
-- imply
  Matrix.rotary' (-φ) = (Matrix.rotary' φ)ᵀ := by
-- proof
  simpa [Matrix.rotary'] using rotaryOn_neg (u := stepEven) (v := stepOdd) φ


-- created on 2026-11-26
