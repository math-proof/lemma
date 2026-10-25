/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry14Bernoullipolymult.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Mathlib.NumberTheory.Bernoulli
import Theorem.Analysis.Ramanujan.Part1Ch7DirichletBeta
import Lemma.Complex.Part1Ch7DirichletBeta
import Lemma.Real.Part1Ch7Entry13Bernoullipolyadd
import Lemma.Real.Ramanujan.Part1Ch7Entry14Bernoulliasymptotic
import Lemma.Real.ExpSubOneMittagLeffler
import Def.Analysis.Ramanujan.Part1Ch7Entry13Bernoullipolyadd
import Def.Analysis.Ramanujan.Part1Ch7Entry14Bernoulliasymptotic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import Def.Analysis.SpecialFunctions.ExpSubOneMittagLeffler
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
