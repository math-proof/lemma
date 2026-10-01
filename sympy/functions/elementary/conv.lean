import Mathlib.Analysis.SpecialFunctions.Exp

/-- py `conv1d/conv2d/conv3d` in a uniform `D`-dimensional form: position `p : Fin D → ℤ`,
kernel taps `t : T` with integer offsets `off t` (dilation and centering folded into `off`),
input channels `c`, output channel `s`. Out-of-range input positions are handled by the caller
(the input function is zero there, i.e. zero padding). -/
def convNd {D d d' : ℕ} {T : Type*} [Fintype T] (off : T → Fin D → ℤ)
    (x : (Fin D → ℤ) → Fin d → ℝ) (w : T → Fin d → Fin d' → ℝ) (p : Fin D → ℤ) (s : Fin d') : ℝ :=
  ∑ t, ∑ c, x (p + off t) c * w t c s


-- created on 2026-09-27
