/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasSequence.lean -/

import Mathlib.Data.Nat.Fib.Basic
/-!
# Lucas sequences

This module defines the two Lucas sequences `U(P, Q)` and `V(P, Q)` for
integer parameters with `Q ≠ 0`.

Sources:

* Christian Ballot, *A Further Generalization of a Congruence of Wolstenholme*,
  Journal of Integer Sequences 15 (2012),
  <https://cs.uwaterloo.ca/journals/JIS/VOL15/Ballot/ballot4.tex>.
* Evis Ieronymou, *Congruences Involving Sums of Ratios of Lucas Sequences*,
  Journal of Integer Sequences 17 (2014),
  <https://cs.uwaterloo.ca/journals/JIS/VOL17/Ieronymou/ier5.tex>.
* Tian-Xiao He, *Impulse Response Sequences and Construction of Number Sequence
  Identities*, Journal of Integer Sequences 16 (2013),
  <https://cs.uwaterloo.ca/journals/JIS/VOL16/He/he13.tex>.
-/


namespace MetaMathlibExt

/-- Integer parameters for a pair of Lucas sequences. The source convention
requires the second parameter to be nonzero. -/
structure LucasSequenceParams where
  p : ℤ
  q : ℤ
  q_ne_zero : q ≠ 0

end MetaMathlibExt
