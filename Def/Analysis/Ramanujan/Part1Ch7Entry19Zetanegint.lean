/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry19Zetanegint.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.Meromorphic.Basic
public import Def.Analysis.Ramanujan.Part1Ch7Phi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.LSeries.ZMod
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Basic

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry19Zetanegint

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

set_option backward.proofsInPublic true in
def chapter7Entry19Left (p q : ℕ) (hp : 0 < p) (hpq : p < q) (r : ℂ) : ℂ :=
  Complex.cpow ((2 * Real.pi * q : ℝ) : ℂ) r / (4 * Complex.Gamma r) *
    (chapter7Phi (r - 1) ⟨(p : ℝ) / q - 1, by
        constructor
        · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          have := div_pos hp0 hq0
          linarith
        · have hpqr : (p : ℝ) < q := by exact_mod_cast hpq
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          exact sub_neg.mpr ((div_lt_one hq0).2 hpqr)⟩ -
      chapter7Phi (r - 1) ⟨-((p : ℝ) / q), by
        constructor
        · have hpqr : (p : ℝ) < q := by exact_mod_cast hpq
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          linarith [((div_lt_one hq0).2 hpqr)]
        · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          exact neg_neg_of_pos (div_pos hp0 hq0)⟩)

set_option backward.proofsInPublic true in
def chapter7Entry19Right (p q : ℕ) (r : ℂ) : ℂ :=
  Complex.sin (Real.pi * r / 2) *
    ∑ j ∈ (Icc 1 ((q - 1) / 2)).attach,
      (Real.sin (2 * Real.pi * (j : ℕ) * p / q) : ℂ) *
        (chapter7Phi (-r) ⟨(j : ℕ) / (q : ℝ) - 1, by
            have hjmem : (j : ℕ) ∈ Icc 1 ((q - 1) / 2) := j.property
            have hj0 : 0 < (j : ℕ) := by
              have := (Finset.mem_Icc.mp hjmem).1
              omega
            have hjq : (j : ℕ) < q := by
              have := (Finset.mem_Icc.mp hjmem).2
              omega
            constructor
            · have hj0r : (0 : ℝ) < (j : ℕ) := by exact_mod_cast hj0
              have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hjq
              linarith [div_pos hj0r hq0]
            · have hjqr : ((j : ℕ) : ℝ) < q := by exact_mod_cast hjq
              have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hjq
              exact sub_neg.mpr ((div_lt_one hq0).2 hjqr)⟩ -
          chapter7Phi (-r) ⟨-((j : ℕ) / (q : ℝ)), by
            have hjmem : (j : ℕ) ∈ Icc 1 ((q - 1) / 2) := j.property
            have hj0 : 0 < (j : ℕ) := by
              have := (Finset.mem_Icc.mp hjmem).1
              omega
            have hjq : (j : ℕ) < q := by
              have := (Finset.mem_Icc.mp hjmem).2
              omega
            constructor
            · have hjqr : ((j : ℕ) : ℝ) < q := by exact_mod_cast hjq
              have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hjq
              linarith [((div_lt_one hq0).2 hjqr)]
            · have hj0r : (0 : ℝ) < (j : ℕ) := by exact_mod_cast hj0
              have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hjq
              exact neg_neg_of_pos (div_pos hj0r hq0)⟩)

end
end Entry19Zetanegint
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
