module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Analysis.SpecialFunctions.GaussHypergeometricSummationFrisch

@[expose] public section

open Finset Filter Topology

/-!
# Gauss summation specialized to Frisch's binomial identity
-/


namespace MetaMathlibExt

section

noncomputable def tterm (A C β : ℝ) (k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval A * (ascPochhammer ℝ k).eval β /
    ((ascPochhammer ℝ k).eval C * (Nat.factorial k : ℝ))

noncomputable def vterm (A C β : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (ascPochhammer ℝ (k + 1)).eval A * (ascPochhammer ℝ k).eval (β + 1) /
    ((ascPochhammer ℝ k).eval C * (Nat.factorial k : ℝ))

end
end MetaMathlibExt
