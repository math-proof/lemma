/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FrobeniusPseudoprime.lean -/

/-
Tests for the Frobenius pseudoprime formalization.
Exercises every public declaration, checks boundary cases `n = 1`, `n = 2`,
and nonmonic `0`, and gives concrete gcmd examples including the composite
ring `ZMod 6`. No nontrivial Frobenius pseudoprime is exhibited.
-/
import sympy.atlas.NumberTheory.FrobeniusPseudoprime
import Lemma.Nat.FrobeniusPseudoprime

#check @Polynomial.IsGreatestCommonMonicDivisor
#check @Nat.IsFrobeniusProbablePrime
#check @Nat.IsFrobeniusPseudoprime
#check @Polynomial.IsGreatestCommonMonicDivisor.unfold
#check @Nat.IsFrobeniusProbablePrime.unfold
#check @Nat.IsFrobeniusProbablePrime.monic
#check @Nat.IsFrobeniusProbablePrime.odd
#check @Nat.IsFrobeniusProbablePrime.one_lt
#check @Nat.IsFrobeniusPseudoprime.unfold
#check @Nat.IsFrobeniusPseudoprime.composite
#check @Nat.IsFrobeniusPseudoprime.probablePrime

/-- `n = 1` cannot satisfy the probable-prime predicate. -/
example (f : Polynomial ℤ) : ¬ Nat.IsFrobeniusProbablePrime 1 f := by
  intro h
  have h1 := Nat.IsFrobeniusProbablePrime.one_lt h
  omega

/-- `n = 2` cannot satisfy the probable-prime predicate. -/
example (f : Polynomial ℤ) : ¬ Nat.IsFrobeniusProbablePrime 2 f := by
  intro h
  have hO := Nat.IsFrobeniusProbablePrime.odd h
  exact (by decide : ¬ Odd (2 : ℕ)) hO

/-- The nonmonic zero polynomial cannot satisfy the probable-prime predicate. -/
example (n : ℕ) : ¬ Nat.IsFrobeniusProbablePrime n 0 := by
  intro h
  have hm := Nat.IsFrobeniusProbablePrime.monic h
  exact (by decide : ¬ (0 : Polynomial ℤ).Monic) hm

/-- Reflexive gcmd example over `ZMod 5`. -/
example : Polynomial.IsGreatestCommonMonicDivisor
    (Polynomial.X : Polynomial (ZMod 5)) Polynomial.X Polynomial.X :=
  ⟨Polynomial.monic_X, Polynomial.monic_X, Polynomial.monic_X, by simp⟩

/-- Reflexive gcmd example at `1` over `ZMod 7`. -/
example : Polynomial.IsGreatestCommonMonicDivisor (1 : Polynomial (ZMod 7)) 1 1 :=
  ⟨Polynomial.monic_one, Polynomial.monic_one, Polynomial.monic_one, by simp⟩

/-- Reflexive gcmd example over the composite ring `ZMod 6`. -/
example : Polynomial.IsGreatestCommonMonicDivisor
    (Polynomial.X : Polynomial (ZMod 6)) Polynomial.X Polynomial.X :=
  ⟨Polynomial.monic_X, Polynomial.monic_X, Polynomial.monic_X, by simp⟩

/-- Projecting monicity from a probable-prime hypothesis. -/
example {n : ℕ} {f : Polynomial ℤ}
    (h : Nat.IsFrobeniusProbablePrime n f) : f.Monic :=
  Nat.IsFrobeniusProbablePrime.monic h

/-- Projecting oddness from a probable-prime hypothesis. -/
example {n : ℕ} {f : Polynomial ℤ}
    (h : Nat.IsFrobeniusProbablePrime n f) : Odd n :=
  Nat.IsFrobeniusProbablePrime.odd h

/-- Projecting the lower bound from a probable-prime hypothesis. -/
example {n : ℕ} {f : Polynomial ℤ}
    (h : Nat.IsFrobeniusProbablePrime n f) : 1 < n :=
  Nat.IsFrobeniusProbablePrime.one_lt h

/-- Projecting compositeness from a pseudoprime hypothesis. -/
example {n : ℕ} {f : Polynomial ℤ}
    (h : Nat.IsFrobeniusPseudoprime n f) : ¬ n.Prime :=
  Nat.IsFrobeniusPseudoprime.composite h

/-- Projecting the probable-prime fact from a pseudoprime hypothesis. -/
example {n : ℕ} {f : Polynomial ℤ}
    (h : Nat.IsFrobeniusPseudoprime n f) : Nat.IsFrobeniusProbablePrime n f :=
  Nat.IsFrobeniusPseudoprime.probablePrime h
