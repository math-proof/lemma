/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/BurnsidePaqb.lean -/


import Lemma.Nat.IsSolvableG.of.EqCardG_MulPowS.Prime.Prime
import Mathlib.Data.ZMod.Basic
open BurnsidePaqb

/-!
# Compile-time tests for Burnside's `p^a q^b` theorem

Authors: Muse Spark 1.3
-/


-- Exact API shape of the headline theorem.
example {G : Type*} [Group G] [Fintype G]
    (p q a b : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hcard : Fintype.card G = p ^ a * q ^ b) : Group.IsSolvable G :=
  burnside_paqb p q a b hp hq hcard

-- Boundary convention `p = q`: a group of order `2 ^ 1 * 2 ^ 1`.
example : Group.IsSolvable (Multiplicative (ZMod 4)) :=
  burnside_paqb 2 2 1 1 (by decide) (by decide) (by decide)

-- Boundary convention with zero exponent `a = 0`: order `2 ^ 0 * 3 ^ 1`.
example : Group.IsSolvable (Multiplicative (ZMod 3)) :=
  burnside_paqb 2 3 0 1 (by decide) (by decide) (by decide)

-- Trivial group with `a = b = 0`: order `2 ^ 0 * 3 ^ 0`.
example : Group.IsSolvable Unit :=
  burnside_paqb 2 3 0 0 (by decide) (by decide) (by simp)

