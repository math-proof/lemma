/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Meromorphic.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Phi
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 20

Reflection identity for a generalized Bernoulli sum at thirds.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry20Generalizedbernoullisum

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

set_option backward.proofsInPublic true in
def chapter7Entry20Left (r : ℂ) : ℂ :=
  Complex.cpow ((6 * Real.pi : ℝ) : ℂ) r /
      (((2 * Real.sqrt 3 : ℝ) : ℂ) * Complex.Gamma r) *
    (chapter7Phi (r - 1) ⟨-1 / 3, by
        change (-1 : ℝ) < -1 / 3 ∧ (-1 / 3 : ℝ) < 0
        norm_num⟩ -
      chapter7Phi (r - 1) ⟨-2 / 3, by
        change (-1 : ℝ) < -2 / 3 ∧ (-2 / 3 : ℝ) < 0
        norm_num⟩)

set_option backward.proofsInPublic true in
def chapter7Entry20Right (r : ℂ) : ℂ :=
  Complex.sin (Real.pi * r / 2) *
    (chapter7Phi (-r) ⟨-1 / 3, by
        change (-1 : ℝ) < -1 / 3 ∧ (-1 / 3 : ℝ) < 0
        norm_num⟩ -
      chapter7Phi (-r) ⟨-2 / 3, by
        change (-1 : ℝ) < -2 / 3 ∧ (-2 / 3 : ℝ) < 0
        norm_num⟩)

-- === Circle parameters ===
private def a1 : UnitAddCircle := (((1/3 : ℝ)) : UnitAddCircle)
private def a2 : UnitAddCircle := (((2/3 : ℝ)) : UnitAddCircle)

-- === Series for triplication ===
private noncomputable def useries (s : ℂ) : ℕ → ℂ :=
  fun n => ↑(Real.sin (2 * Real.pi * (1/3 : ℝ) * ((n : ℕ) : ℝ))) / ((n : ℕ) : ℂ) ^ s

private noncomputable def oddseries (s : ℂ) : ℕ → ℂ :=
  fun n => (1 / ((n : ℂ) + ((1/3 : ℝ) : ℂ)) ^ s - 1 / ((n : ℂ) + 1 - ((1/3 : ℝ) : ℂ)) ^ s) / 2

private noncomputable def fseries (s : ℂ) : ℕ → ℂ :=
  fun k => 1 / ((3 * k + 1 : ℕ) : ℂ) ^ s - 1 / ((3 * k + 2 : ℕ) : ℂ) ^ s

private def blk : ℕ × Fin 3 → ℕ := fun p => 3 * p.1 + p.2.val
end
end Entry20Generalizedbernoullisum
