/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RidoutPadicRoth.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Int.NatAbs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators

/-!
This file proves Ridout's p-adic extension of Roth's theorem for rational approximation of
real algebraic irrational numbers at a finite set of primes.
-/


namespace MetaMathlibExt

noncomputable def ridoutNumPart (S : Finset Nat.Primes) (r : ℚ) : ℕ :=
  ∏ l ∈ S, l.1 ^ padicValInt l.1 r.num

noncomputable def ridoutDenPart (S : Finset Nat.Primes) (r : ℚ) : ℕ :=
  ∏ l ∈ S, l.1 ^ padicValNat l.1 r.den

def ridoutHeight (r : ℚ) : ℕ :=
  max r.num.natAbs r.den

noncomputable def ridoutApproximants
    (ξ ε : ℝ) (S : Finset Nat.Primes) : Set ℚ :=
  {r : ℚ |
    ((∏ q ∈ S,
      padicNorm q.1 (r.num : ℚ) * padicNorm q.1 (r.den : ℚ) : ℚ) : ℝ) *
        |ξ - (r : ℝ)| <
      (((ridoutHeight r : ℕ) : ℝ) ^ (2 + ε))⁻¹}

end MetaMathlibExt
