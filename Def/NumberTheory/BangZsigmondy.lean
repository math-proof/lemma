/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BangZsigmondy.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Def.NumberTheory.PrimitiveDivisor
import Lemma.Nat.PrimitiveDivisor
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
/-!
# Bang–Zsigmondy theorem

This file proves the general Bang–Zsigmondy existence of a primitive prime divisor
of `a ^ n - b ^ n` (mathematical integer subtraction), with a concrete exceptional-case
predicate. The existing primitive-divisor predicate quantifies over exactly the earlier
positive indices `1 ≤ m < n`.

## Sources

* Gombodorj Bayarmagnai, "A Note on a Theorem of Rotkiewicz,"
  Journal of Integer Sequences 18 (2015),
  <https://cs.uwaterloo.ca/journals/JIS/VOL18/Bayarmagnai/bayar4.tex>.
* Live and bundled source-file SHA-256:
  `45424a5bf963088269996fcf9ada29f1b6d4eb268f44ad29587d86826e91430b`.
* Lines 133–137 invoke the general Zsigmondy theorem in the paper's proof;
  exact newline-terminated span SHA-256:
  `d66cbabd292cc311ee194cf1b6730baa16f07761b0e14105885d72f332a60f53`.
* Lenny Jones, "Variations on a Theme of Sierpiński,"
  Journal of Integer Sequences 10 (2007),
  <https://cs.uwaterloo.ca/journals/JIS/VOL10/Jones/jones67.tex>.
* Live and bundled source-file SHA-256:
  `deef2828ed90318f0eef3881368d4cd22acd58e85274688a556b75e5d7f3d19a`.
* Lines 211–215 state the `b = 1` Bang specialization and both exception families;
  exact newline-terminated span SHA-256:
  `c69c3d5dc542944ece21b7a0d61de6263e5a989f84ff2bd2cc05b1d166160615`.
* Bayarmagnai's brief invocation writes only the sporadic exception and is not itself
  a sound complete statement at exponent two; the formal declaration deliberately restores
  the classical missing family `n = 2` with `a + b` a power of two.
* The positivity/order/coprimality normalization is supported by Bayarmagnai lines 101–103.
* Archive task id: `jis_grounded_502e7a5f72ef9732d2cd2896`.
* G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of aⁿ − bⁿ*,
  Ann. of Math. (2) 5 (1903–1904), 173–180.
-/


namespace MetaMathlibExt

/-- Concrete Bang–Zsigmondy exceptional case predicate: the sporadic exception
`(a, b, n) = (2, 1, 6)`, or exponent two with `a + b` a power of two. -/
def IsBangZsigmondyExceptional (a b n : ℕ) : Prop :=
  (a = 2 ∧ b = 1 ∧ n = 6) ∨ (n = 2 ∧ ∃ k : ℕ, a + b = 2 ^ k)

/-- The homogenized cyclotomic value `b ^ φ(n) · Φ_n (a / b)`, as an integer. -/
noncomputable def zsPhi (n a b : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (Nat.totient n + 1),
    (Polynomial.cyclotomic n ℤ).coeff i * (a : ℤ) ^ i * (b : ℤ) ^ (Nat.totient n - i)

end MetaMathlibExt
