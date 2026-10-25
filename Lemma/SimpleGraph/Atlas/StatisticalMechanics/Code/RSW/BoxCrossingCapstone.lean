import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.RSW.BoxCrossingCapstone
open StatMech StatMech.RSW


/--
[boxCrossing_uniform_of_p4_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingCapstone.lean)
-/
@[path]
private lemma boxCrossing_uniform_of_p4_inputs_eq
  {ξ₀ : Ξ}
  {μ : Ξ → ℕ → Set (ConfigSpace (Sym2 (Lattice.Site 2))) → ℝ}
  {ν : ℕ → ℕ → Set (ConfigSpace (Sym2 (Lattice.Site 2))) → ℝ}
  {a : ℕ → ℝ}
-- given
  (hnn : ∀ n, 0 ≤ a n)
  (hle1 : ∀ n, a n ≤ 1)
  (hanti : Antitone a)
  (hsub : ∀ m n, a (m + n) ≤ a m * a n)
  (hP4 : P4ImpliesP5.rp4_P4 a)
  (hdich : rp5_P5b ν ∨ P4ImpliesP5.rp4_StretchedExpDecay a)
  (hcmp : ∀ R n, μ ξ₀ n (annulusEvent n) ≤ ν R n (annulusEvent n))
  (hglue : ∀ n, μ ξ₀ n (boxCrossingEvent 10 n) ^ 4 ≤ μ ξ₀ n (annulusEvent n))
  (hchain : ∀ α n, ν 2 n (annulusEvent n) ≤ μ ξ₀ n (boxCrossingEvent α n))
  (htwo : ∀ α, 0 < α → ∃ c, 0 < c ∧ ∀ ξ n, c ≤ μ ξ n (boxCrossingEvent α n) ∧ μ ξ n (boxCrossingEvent α n) ≤ 1 - c) :
-- imply
  P5c μ := by
-- proof
  apply StatMech.RSW.boxCrossing_uniform_of_p4_inputs ξ₀ a hnn hle1 hanti hsub hP4 hdich hcmp hglue hchain htwo


-- created on 2026-10-23
