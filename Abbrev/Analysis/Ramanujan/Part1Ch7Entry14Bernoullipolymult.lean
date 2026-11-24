module
public import Mathlib.NumberTheory.Bernoulli
public import Theorem.Analysis.Ramanujan.Part1Ch7DirichletBeta
public import Theorem.Complex.Part1Ch7DirichletBeta
public import Theorem.Real.Part1Ch7Entry13Bernoullipolyadd
public import Theorem.Real.Ramanujan.Part1Ch7Entry14Bernoulliasymptotic
public import Theorem.Real.ExpSubOneMittagLeffler
public import Def.Analysis.Ramanujan.Part1Ch7Entry13Bernoullipolyadd
public import Def.Analysis.Ramanujan.Part1Ch7Entry14Bernoulliasymptotic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic
public import Def.Analysis.SpecialFunctions.ExpSubOneMittagLeffler


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry14Bernoullipolymult.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/
/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 14

This file proves the convergence and finite-order asymptotic expansion of Ramanujan's
Bernoulli-polynomial series in terms of the Stieltjes constants.
-/
namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry14Bernoullipolymult

open scoped Nat Real BigOperators Interval

open Asymptotics Filter Finset Topology MeasureTheory

noncomputable section

abbrev entry14Remainder := MetaMathlibExt.oneDivExpSubOneLaurentRemainder

end
end Entry14Bernoullipolymult
end MathlibExt.Analysis.Ramanujan.Part1Ch7
