import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part3
set_option doc.verso.suggestions false


def UniformConvergesTo {X:Type*} (f: ℕ → X → EReal) (g: X → EReal) : Prop := ∀ ε:NNReal, ε > 0 → ∃ N:ℕ, ∀ n ≥ N, ∀ x, f n x > g x - ε ∧ f n x < g x + ε

/-!
## Remark 1.3.10: Measurable functions can have non-measurable preimages

We construct an example showing that even for a measurable function f: ℝ^d → \[0, +∞\],
the inverse image f⁻¹(E) of a Lebesgue measurable set E need not be Lebesgue measurable.

**Strategy** (from the textbook):
1. The Cantor set C := \{∑ aⱼ 3^(-j) : aⱼ ∈ \{0,2\}\} has measure zero
2. Define f: \[0,1\] → C by mapping binary digits to ternary: f(∑ bⱼ 2^(-j)) = ∑ 2bⱼ 3^(-j)
3. f is bijective from A (non-terminating binary decimals) onto C, and f is measurable
4. Take non-measurable F ⊆ A (from Vitali construction)
5. E := f(F) ⊆ C is measurable (subset of null set), but f⁻¹(E) = F is non-measurable

**Implementation note**: Our formalization differs slightly from the textbook:
- **Textbook**: f(x) = 0 for dyadic rationals (terminating binary decimals)
- **Our version**: f is defined uniformly for all x ∈ \[0,1\] using floor-based binary digits

The textbook's f is NOT monotone on \[0,1\] (e.g., f(0.4) > 0 but f(0.5) = 0).
Our f IS monotone on all of \[0,1\], which simplifies the measurability proof:
sublevel sets are intervals, hence measurable by Lemma 1.3.9(viii).

Both versions work for the theorem because:
- Both are injective on A (non-dyadic numbers have unique binary expansions)
- Both map \[0,1\] into {name}`CantorSet` ∪ \{0\}
- Both give measurable f with f⁻¹(E) = F non-measurable
-/

/-- Dyadic rationals: numbers of the form k/2^n where k ≤ 2^n.
    These are exactly the real numbers with terminating binary expansions. -/
def DyadicRationals : Set ℝ := {x : ℝ | ∃ (k n : ℕ), x = k / 2^n ∧ k ≤ 2^n}

