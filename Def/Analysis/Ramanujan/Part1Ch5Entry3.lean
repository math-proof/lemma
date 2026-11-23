/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry3.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Data.Complex.Basic
public import Def.Analysis.Ramanujan.Part1Ch5Entry1Euleriangf
public import Theorem.Real.Part1Ch5Entry1Euleriangf
public import Theorem.Complex.Part1Ch5Entry4
public import Def.Analysis.Ramanujan.Part1Ch5Entry4
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SimpRw

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 3

For `p ≠ -1`, the operator `φ ↦ ∑ aₙ hⁿ φ⁽ⁿ⁾` with
`aₙ = (-1)ⁿ ψₙ(p) / (n! (p + 1)ⁿ⁺¹)`, where `ψₙ` is the Eulerian polynomial evaluated at
`-p`, inverts `φ(x) ↦ φ(x + h) + p φ(x)` on complex polynomials, and no other coefficient
sequence does.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry3

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

open Entry1Euleriangf Entry4

noncomputable section

def chapter5Entry3Coeff (n : ℕ) (p : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * chapter5Psi n p /
    ((n.factorial : ℂ) * (p + 1) ^ (n + 1))

def auxRec (p : ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ k : ℕ, (∑ n ∈ range (k + 1), a n * ((Nat.descFactorial k n : ℕ) : ℂ)) +
    p * (a k * ((k.factorial : ℕ) : ℂ)) = if k = 0 then 1 else 0

noncomputable def auxQ (j : ℕ) (t : ℂ) : ℂ :=
  ∑ i ∈ range (j + 1), (eulerianNumber j i : ℂ) * t ^ i

noncomputable def auxV (j : ℕ) (t : ℂ) : ℂ :=
  ∑ i ∈ range (j + 1), (i : ℂ) * (eulerianNumber j i : ℂ) * t ^ i

noncomputable def auxS (k : ℕ) (t : ℂ) : ℂ :=
  ∑ j ∈ range (k + 1), (Nat.choose k j : ℂ) * auxQ j t * (t - 1) ^ (k - j)

noncomputable def auxM (k : ℕ) (t : ℂ) : ℂ := auxS k t - t * auxQ k t

noncomputable def Qpoly (j : ℕ) : Polynomial ℂ :=
  ∑ i ∈ range (j + 1), Polynomial.C (eulerianNumber j i : ℂ) * Polynomial.X ^ i

noncomputable def Vpoly (j : ℕ) : Polynomial ℂ :=
  ∑ i ∈ range (j + 1),
    Polynomial.C ((i : ℂ) * (eulerianNumber j i : ℂ)) * Polynomial.X ^ i

noncomputable def Spoly (k : ℕ) : Polynomial ℂ :=
  ∑ j ∈ range (k + 1),
    Polynomial.C (Nat.choose k j : ℂ) * Qpoly j * (Polynomial.X - 1) ^ (k - j)

noncomputable def Tpoly (k : ℕ) : Polynomial ℂ :=
  ∑ i ∈ range (k + 1),
    Polynomial.C (Nat.choose k i : ℂ) * Qpoly (i + 1) *
      (Polynomial.X - 1) ^ (k - i)

noncomputable def Upoly (k : ℕ) : Polynomial ℂ :=
  ∑ j ∈ range (k + 1),
    Polynomial.C (Nat.choose k j : ℂ) * Vpoly j * (Polynomial.X - 1) ^ (k - j)

noncomputable def Mpoly (k : ℕ) : Polynomial ℂ :=
  Spoly k - Polynomial.X * Qpoly k

end
end Entry3
end MathlibExt.Analysis.Ramanujan.Part1Ch5
