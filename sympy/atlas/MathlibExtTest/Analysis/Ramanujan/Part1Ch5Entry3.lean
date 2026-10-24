/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch5Entry3.lean -/


import sympy.atlas.Analysis.Ramanujan.Part1Ch5Entry3
import Lemma.Real.Ramanujan.Part1Ch5Entry3

/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 3 API checks

The coefficients (built on Entry 4's Eulerian data), the shift, and direct uses of the exported
inversion theorem.
-/

namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch5Entry3

open Polynomial MathlibExt.Analysis.Ramanujan.Part1Ch5 MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry3
  MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry1Euleriangf
  MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry4

-- The coefficients are defined from Entry 4's Eulerian polynomial.
example (n : ℕ) (p : ℂ) :
    chapter5Entry3Coeff n p =
      (-1 : ℂ) ^ n * chapter5Psi n p /
        ((n.factorial : ℂ) * (p + 1) ^ (n + 1)) := rfl

-- The first coefficient is `1 / (p + 1)`.
example (p : ℂ) : chapter5Entry3Coeff 0 p = 1 / (p + 1) := by
  simp [chapter5Entry3Coeff, chapter5Psi]

-- The shift sends `X` to `X + h`.
example (h : ℂ) : taylor h (X : ℂ[X]) = X + C h := by
  rw [taylor_apply]
  simp

-- The Entry 3 coefficients invert the operator, and no other sequence does.
example (p h : ℂ) (hp : p ≠ -1) (phi : ℂ[X]) :
    taylor h
          (chapter5DerivativeExpansion (fun n => chapter5Entry3Coeff n p) h phi) +
        C p * chapter5DerivativeExpansion (fun n => chapter5Entry3Coeff n p) h phi = phi :=
  (ramanujan_part1_ch5_entry3 p hp).1 h phi

example (p : ℂ) (hp : p ≠ -1) (a : ℕ → ℂ)
    (ha : ∀ (h : ℂ) (phi : ℂ[X]),
      taylor h (chapter5DerivativeExpansion a h phi) +
        C p * chapter5DerivativeExpansion a h phi = phi) :
    a 0 = 1 / (p + 1) := by
  rw [(ramanujan_part1_ch5_entry3 p hp).2 a ha 0]
  simp [chapter5Entry3Coeff, chapter5Psi]

end MathlibExtTest.Analysis.Ramanujan.Part1Ch5Entry3
