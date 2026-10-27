import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Analysis.SpecialFunctions.GaussHypergeometricSummationFrisch
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
