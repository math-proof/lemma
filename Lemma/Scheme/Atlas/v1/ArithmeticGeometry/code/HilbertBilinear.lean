import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.HilbertBilinear
open scoped Classical


/--
[legendreSym_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertBilinear.lean)
-/
@[path]
lemma legendreSym_val
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {a : ZMod p} :
-- imply
  legendreSym p (ZMod.val a : ℤ) = (quadraticChar (ZMod p)) a := by
-- proof
  unfold legendreSym
  congr 1
  simp [ZMod.natCast_val]

/--
[padic_hilbert_mul_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertBilinear.lean)
-/
@[path]
lemma padic_hilbert_mul_left
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b c : ℚ_[p]ˣ} :
-- imply
  padicHilbertSymbol p (a * b) c = padicHilbertSymbol p a c * padicHilbertSymbol p b c := by
-- proof
  simp only [padicHilbertSymbol]
  exact hilbertSymbol.mul_left a b c


-- created on 2026-10-23
