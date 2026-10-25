import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part5
set_option doc.verso.suggestions false


namespace Remark_1_3_10

/-- The properties required of the binary-to-ternary function for this construction.
    The function maps \[0,1\] into the Cantor set C by converting binary digits to ternary.

    Note: Unlike the textbook (which sets g(x) = 0 for dyadic rationals), our g is defined
    uniformly for all x ∈ \[0,1\]. This makes g monotone on ALL of \[0,1\], not just on A. -/
structure BinaryToTernaryProperties (g : ℝ → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ g x
  bounded : ∀ x, g x ≤ 1
  zero_outside : ∀ x, x ∉ Set.Icc 0 1 → g x = 0  -- g(x) = 0 outside [0,1]
  zero_at_zero : g 0 = 0  -- g(0) = 0 (binary 0.000... maps to ternary 0.000...)
  zero_set_countable : (Set.Icc 0 1 ∩ {x | g x = 0}).Countable  -- {g = 0} ∩ [0,1] = {0}
  monotone_on : MonotoneOn g (Set.Icc 0 1)  -- g is monotone on ALL of [0,1]
  image_in_cantor : g '' (Set.Icc 0 1) ⊆ CantorSet ∪ {0}
  injective_on_nonterminating : ∃ A : Set ℝ, A ⊆ Set.Icc 0 1 ∧
    (Set.Icc 0 1 \ A).Countable ∧  -- A is co-countable in [0,1]
    Set.InjOn g A ∧                 -- g is injective on A (hence bijective onto g(A) ⊆ C)
    A ∩ DyadicRationals = ∅         -- A excludes dyadic rationals

end Remark_1_3_10
