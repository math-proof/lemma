/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry5Eulerianexplicit.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Data.Nat.Choose.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch5Entry4
import Lemma.Complex.Part1Ch5Entry4
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 5

Formulas (5.1) and (5.2) of Entry 5 from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985): two finite expansions of the Eulerian polynomial `chapter5Psi n p`.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry5Eulerianexplicit

open scoped Nat BigOperators Polynomial
open Finset Entry4

noncomputable section

def chapter5Entry5Formula51Term (n : ℕ) (p : ℂ) (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k * (n.choose k : ℂ) * chapter5Psi k p /
    (p + 1) ^ k

def chapter5Entry5Formula52Term (n : ℕ) (p : ℂ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j * (n.choose (j + 1) : ℂ) * (p + 1) ^ j *
    chapter5Psi (n - j - 1) p

private noncomputable def Apoly (n : ℕ) : ℂ[X] :=
  ∑ k ∈ range (n + 1), Polynomial.C (eulerianNumber n k : ℂ) * Polynomial.X ^ k

private noncomputable def B (n : ℕ) : ℂ[X] :=
  ∑ i ∈ range (n + 1),
    Polynomial.C (Nat.choose n i : ℂ) * ((Polynomial.X - 1) ^ i * Apoly (n - i))

private noncomputable def cc (n : ℕ) : ℂ[X] :=
  ∑ i ∈ range (n + 1),
    Polynomial.C (Nat.choose n i : ℂ) * ((Polynomial.X - 1) ^ i * Apoly (n + 1 - i))
end
end Entry5Eulerianexplicit
end MathlibExt.Analysis.Ramanujan.Part1Ch5
