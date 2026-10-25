/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GesselWord.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
/-!
# Gessel words

A Gessel word over `S = [n]` is a word over the unbarred and barred copies of
`S` whose reverse-label balance is nonnegative on every prefix.

## References

- [A. Ayyer, *Towards a Human Proof of Gessel's Conjecture*](https://cs.uwaterloo.ca/journals/JIS/VOL12/Ayyer/ayyer7.tex),
  Definition 2 (source statement `jis_610953010c03e4ea40bfef6d`).
-/


namespace MetaMathlibExt

open scoped BigOperators

/-- The Gessel alphabet over `S = [n]`, modeled by an unbarred and a barred copy of `Fin n`.

`Sum.inl` denotes an unbarred letter and `Sum.inr` its barred counterpart. -/
abbrev GesselAlphabet (n : ℕ) : Type :=
  Fin n ⊕ Fin n

end MetaMathlibExt
