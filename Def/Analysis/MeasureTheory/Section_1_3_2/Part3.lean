import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part2
set_option doc.verso.suggestions false


namespace UnsignedMeasurable.TFAE_helpers

variable {d : ℕ} {f : EuclideanSpace' d → EReal}

-- The approximating function: f_n(x) = floor(min(f(x), n) * 2^n) / 2^n when |x| ≤ n, else 0
-- This is the largest k·2^{-n} ≤ min(f(x), n)
private noncomputable def approx_fn (f : EuclideanSpace' d → EReal) (n : ℕ) (x : EuclideanSpace' d) : EReal :=
  if ‖x‖ ≤ n then
    let t := min (f x) n
    if t = ⊥ then 0  -- won't happen for unsigned f
    else if t = ⊤ then n  -- t = min(⊤, n) = n, so this case shouldn't trigger
    else
      let r := t.toReal
      if r < 0 then 0  -- won't happen for unsigned f
      else ((⌊r * 2^n⌋₊ : ℕ) : ℝ) / (2^n : ℝ)
  else 0

end UnsignedMeasurable.TFAE_helpers
