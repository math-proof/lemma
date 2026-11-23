module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/--
Half-split or adjacent-pair plane rotation.

`u t` and `v t` are the two coordinates of plane `t`. Entry `(u t, u t)` is `cos (θ t)`,
`(u t, v t)` is `-sin (θ t)`, `(v t, u t)` is `sin (θ t)`, and `(v t, v t)` is `cos (θ t)`.
-/
noncomputable def Matrix.rotaryOn {d : ℕ} (u v : Fin d → Fin (d + d)) (θ : Fin d → ℝ) :
    Matrix (Fin (d + d)) (Fin (d + d)) ℝ :=
  Matrix.of fun i j =>
    ∑ t : Fin d, (
      (if i = u t ∧ j = u t then Real.cos (θ t) else 0) +
      (if i = u t ∧ j = v t then -Real.sin (θ t) else 0) +
      (if i = v t ∧ j = u t then Real.sin (θ t) else 0) +
      (if i = v t ∧ j = v t then Real.cos (θ t) else 0))

/-- Even coordinate `2t` of an interleaved pair in `Fin (d + d)`. -/
def Matrix.ropeEven (d : ℕ) (t : Fin d) : Fin (d + d) :=
  ⟨2 * (t : ℕ), by
    have ht := t.isLt
    omega⟩

/-- Odd coordinate `2t + 1` of an interleaved pair in `Fin (d + d)`. -/
def Matrix.ropeOdd (d : ℕ) (t : Fin d) : Fin (d + d) :=
  ⟨2 * (t : ℕ) + 1, by
    have ht := t.isLt
    omega⟩

/--
Hugging Face `rotate_half` matrix: planes are `(t, t + d)`.

\[
\begin{pmatrix}
\cos\theta & -\sin\theta \\
\sin\theta & \cos\theta
\end{pmatrix}
\]
on each pair, written as the four blocks of shape `d × d`.
-/
noncomputable def Matrix.rotary {d : ℕ} (θ : Fin d → ℝ) : Matrix (Fin (d + d)) (Fin (d + d)) ℝ :=
  Matrix.rotaryOn (Fin.castAdd d) (Fin.natAdd d) θ

/--
Su et al. interleaved rotary matrix: planes are `(2t, 2t + 1)`.
-/
noncomputable def Matrix.rotary' {d : ℕ} (θ : Fin d → ℝ) : Matrix (Fin (d + d)) (Fin (d + d)) ℝ :=
  Matrix.rotaryOn (Matrix.ropeEven d) (Matrix.ropeOdd d) θ

namespace Function

/-- Field-notation form of `Matrix.rotary` on a plain row `θ : Fin d → ℝ`, so `θ[i].rotary`
works when a matrix row is a plain function. -/
noncomputable def rotary {d : ℕ} (θ : Fin d → ℝ) : Matrix (Fin (d + d)) (Fin (d + d)) ℝ :=
  Matrix.rotary θ

/-- Field-notation form of `Matrix.rotary'` on a plain row `θ : Fin d → ℝ`. -/
noncomputable def rotary' {d : ℕ} (θ : Fin d → ℝ) : Matrix (Fin (d + d)) (Fin (d + d)) ℝ :=
  Matrix.rotary' θ

end Function
