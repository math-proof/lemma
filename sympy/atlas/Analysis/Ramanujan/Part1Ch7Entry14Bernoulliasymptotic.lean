/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry14Bernoulliasymptotic.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Avocado, Codex
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry13Bernoullipolyadd
import Lemma.Real.Part1Ch7Entry13Bernoullipolyadd
import Lemma.Real.Ramanujan.Part1Ch7Entry13Bernoullirecurrence
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry13Bernoullirecurrence
section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry14Bernoulliasymptotic

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7Entry14Cor2LeftTerm (s : ℝ) (j : ℕ) : ℝ :=
  let k : ℝ := j + 2
  1 / (Real.rpow k (s + 1) * Real.log k)

def chapter7StieltjesA (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * c k / (k.factorial : ℝ)

def chapter7Entry14Cor2ConstantTerm (c : ℕ → ℝ) (j : ℕ) : ℝ :=
  chapter7StieltjesA c (j + 1) / (j + 2)

def chapter7Entry14Cor2Constant (c : ℕ → ℝ) : ℝ :=
  (∑' j : ℕ, chapter7Entry14Cor2LeftTerm 1 j) - 1 +
    Real.eulerMascheroniConstant +
      ∑' j : ℕ, chapter7Entry14Cor2ConstantTerm c j

def chapter7Entry14Cor2PowerTerm (c : ℕ → ℝ) (s : ℝ) (j : ℕ) : ℝ :=
  chapter7StieltjesA c (j + 1) * s ^ (j + 2) / (j + 2)

def chapter7StieltjesApprox (k m : ℕ) : ℝ :=
  (∑ j ∈ Icc 1 m, Real.log (j : ℝ) ^ k / j) -
    Real.log (m : ℝ) ^ (k + 1) / (k + 1)
end
end Entry14Bernoulliasymptotic
end MathlibExt.Analysis.Ramanujan.Part1Ch7
