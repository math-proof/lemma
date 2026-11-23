/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry18Bernoullidiff.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.NumberTheory.LSeries.ZMod
public import Theorem.Analysis.Ramanujan.Part1Ch7DirichletBeta
public import Theorem.Complex.Part1Ch7DirichletBeta
public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SimpRw

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 18

Functional equation of the Dirichlet beta function.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry18Bernoullidiff

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

open DirichletBeta

noncomputable section

def chapter7Entry18FunctionalRight (r : ℂ) : ℂ :=
  Complex.cos (Real.pi * r / 2) *
    Complex.cpow ((Real.pi / 2 : ℝ) : ℂ) (r - 1) *
      Complex.Gamma (1 - r) * chapter7DirichletBeta (1 - r)

def chapter7Entry18Left (r : ℂ) : ℂ :=
  Complex.cos (Real.pi * r / 2) * chapter7EulerStar (1 - r)

def chapter7Entry18Middle (r : ℂ) : ℂ :=
  2 * chapter7DirichletBeta r

def chapter7Entry18Right (r : ℂ) : ℂ :=
  Complex.cpow ((Real.pi / 2 : ℝ) : ℂ) r * chapter7EulerStar r /
    Complex.Gamma r

end
end Entry18Bernoullidiff
end MathlibExt.Analysis.Ramanujan.Part1Ch7
