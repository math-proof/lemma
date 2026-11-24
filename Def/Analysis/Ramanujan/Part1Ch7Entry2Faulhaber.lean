module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Basic
public import Def.Analysis.Ramanujan.Part1Ch7Entry10Zeta4
public import Theorem.Real.Ramanujan.Part1Ch7Entry10Zeta4
public import Theorem.Nat.LSeries.RiemannZeta
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.LSeries.ZMod
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Abbrev.Analysis.Ramanujan.Part1Ch7Entry2Faulhaber


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry2Faulhaber.lean -/
/-
Author: @akiezun, Avocado
-/
/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/
section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry2Faulhaber

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7Entry2Value (r : ℂ) : ℂ :=
  (Complex.cpow 2 (r + 1) - 1) * chapter7BernoulliStar (r + 1) *
    Complex.sin ((Real.pi : ℂ) * r / 2) / (r + 1)

def chapter7Eta (s : ℂ) : ℂ :=
  if s = 1 then (Real.log 2 : ℂ)
  else (1 - Complex.cpow 2 (1 - s)) * riemannZeta s

def chapter7NatCpow (n : ℕ) (r : ℂ) : ℂ :=
  Complex.cpow (n : ℂ) r

def chapter7EtaTerm (s : ℂ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j / chapter7NatCpow (j + 1) s

def chapter7EtaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ range N, chapter7EtaTerm s j

-- The exceptional set for the functional equation.
def chapter7Entry2BadSet : Set ℂ := {r : ℂ | ∃ n : ℕ, r = -(n : ℂ)}

noncomputable def chapter7EtaChar : ZMod 2 → ℂ :=
  fun a => if a = 0 then -1 else 1

noncomputable def chapter7EtaPair (n : ℕ) (s : ℂ) : ℂ :=
  chapter7EtaTerm s (2 * n) + chapter7EtaTerm s (2 * n + 1)

noncomputable def chapter7EtaPairTsum (s : ℂ) : ℂ :=
  ∑' n : ℕ, chapter7EtaPair n s

end
end Entry2Faulhaber
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
