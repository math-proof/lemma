/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry2Faulhaber.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Set.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Def.Analysis.Ramanujan.Part1Ch7Entry10Zeta4
import Lemma.Real.Ramanujan.Part1Ch7Entry10Zeta4
import Lemma.Nat.LSeries.RiemannZeta
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Abbrev.Analysis.Ramanujan.Part1Ch7Entry2Faulhaber
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
