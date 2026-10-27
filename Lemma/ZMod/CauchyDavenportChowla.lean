import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.Additive.CauchyDavenportChowla
open scoped Pointwise


/--
[CauchyDavenportChowla](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/CauchyDavenportChowla.lean)
-/
@[path]
private lemma cauchy_davenport_chowla_le
-- given
  (q : ℕ)
  (A B : Finset (ZMod q))
  (hq : 0 < q)
  (hA : A.Nonempty)
  (hB : B.Nonempty)
  (h0 : (0 : ZMod q) ∈ B)
  (hunit : ∀ b ∈ B, b ≠ (0 : ZMod q) → IsUnit b) :
-- imply
  min q (A.card + B.card - 1) ≤ (A + B).card := by
-- proof
  apply MathlibExt.Combinatorics.Additive.CauchyDavenportChowlaWanted.cauchy_davenport_chowla
    q A B hq hA hB h0 hunit


-- created on 2026-10-11
