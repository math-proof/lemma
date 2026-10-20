/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Hinge.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hinge theorem

This file proves Euclid's hinge theorem for the Euclidean plane by expanding squared norms with
the vector law of cosines.
-/

namespace MetaMathlibExt

private theorem hinge_opposite_side_sq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (A B C : V) :
    ‖C - B‖ ^ 2 =
      ‖C - A‖ ^ 2 - 2 * inner ℝ (C - A) (B - A) + ‖B - A‖ ^ 2 := by
  rw [show C - B = (C - A) - (B - A) by abel]
  exact norm_sub_sq_real (C - A) (B - A)

private theorem hinge_sq_lt {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A B C D E F : V)
    (hAB : ‖B - A‖ = ‖E - D‖) (hAC : ‖C - A‖ = ‖F - D‖)
    (hinner : inner ℝ (B - A) (C - A) < inner ℝ (E - D) (F - D)) :
    ‖F - E‖ ^ 2 < ‖C - B‖ ^ 2 := by
  rw [hinge_opposite_side_sq D E F, hinge_opposite_side_sq A B C]
  rw [real_inner_comm (E - D) (F - D), real_inner_comm (B - A) (C - A)]
  rw [← hAC, ← hAB]
  linarith

private theorem hinge_norm_lt_of_sq_lt {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {x y : V}
    (h : ‖x‖ ^ 2 < ‖y‖ ^ 2) : ‖x‖ < ‖y‖ :=
  (sq_lt_sq₀ (norm_nonneg x) (norm_nonneg y)).mp h

/-- Hinge theorem for a real inner product space: if two pairs of adjacent sides have equal
lengths and the first included inner product is smaller, then its opposite side is longer.
Source: Euclid's *Elements*, Book I, Proposition 24.

Proof: Apply the law of cosines via `norm_sub_sq_real` and compare the squared side lengths.
-/
theorem hinge_theorem_of_inner_lt {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (A B C D E F : V)
    (hAB : ‖B - A‖ = ‖E - D‖) (hAC : ‖C - A‖ = ‖F - D‖)
    (hinner : inner ℝ (B - A) (C - A) < inner ℝ (E - D) (F - D)) :
    ‖F - E‖ < ‖C - B‖ :=
  hinge_norm_lt_of_sq_lt (hinge_sq_lt A B C D E F hAB hAC hinner)

/-- Hinge theorem: two nondegenerate (noncollinear) triangles with two pairs of
equal sides (`AB = DE`, `AC = DF`); if the included angle at `A` exceeds the
included angle at `D` (compared via inner products), then the opposite side
`BC` exceeds `EF`.
Source: Euclid's Elements, Book I, Proposition 24
(https://mathcs.clarku.edu/~djoyce/elements/bookI/propI24.html); see also
https://en.wikipedia.org/wiki/Hinge_theorem.

Proves `Wanted` entry `hinge_theorem`.

Proof: Mathlib's vector law of cosines, `norm_sub_sq_real`, compares the squared opposite-side
lengths, following Euclid's *Elements*, Book I, Proposition 24.
-/
theorem hinge_theorem : ∀ (A B C D E F : EuclideanSpace ℝ (Fin 2)),
  B ≠ A → C ≠ A → C ≠ B → E ≠ D → F ≠ D → F ≠ E →
  (∀ t : ℝ, C - A ≠ t • (B - A)) →
  (∀ s : ℝ, F - D ≠ s • (E - D)) →
  ‖B - A‖ = ‖E - D‖ → ‖C - A‖ = ‖F - D‖ →
  inner ℝ (B - A) (C - A) < inner ℝ (E - D) (F - D) →
  ‖F - E‖ < ‖C - B‖ :=
  fun A B C D E F _ _ _ _ _ _ _ _ => hinge_theorem_of_inner_lt A B C D E F

end MetaMathlibExt
