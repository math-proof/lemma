/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PisotNumber.lean -/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.Minpoly.Basic

namespace MetaMathlibExt

/-!
# Pisot numbers

Source: M. Panju, *Beta expansions for regular Pisot numbers*, Journal of Integer Sequences
14 (2011), Article 11.6.4,
[`panju2.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL14/Panju/panju2.tex).
-/

/-- A Pisot number is a real algebraic integer greater than one whose other complex
conjugates all have norm less than one. -/
def IsPisotNumber (q : ℝ) : Prop :=
  IsIntegral ℤ q ∧ 1 < q ∧
    ∀ β ∈ ((minpoly ℤ q).map (Int.castRingHom ℂ)).roots,
      β ≠ (q : ℂ) → ‖β‖ < 1

end MetaMathlibExt
