import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part8
set_option doc.verso.suggestions false


/-- Remark 1.3.10: The inverse image of a Lebesgue measurable set by a measurable function
    need not be Lebesgue measurable.
    Proof: Let f = {name}`Remark_1_3_10.binaryToTernary` (maps \[0,1\] → Cantor set), F ⊆ \[0,1\] non-measurable (Vitali).
    Set E = f(F) ⊆ Cantor set. Then E is null (⊆ null set) hence measurable, but f⁻¹(E) = F
    is non-measurable. (Uses injectivity of f on non-dyadic rationals A ⊇ F.) -/
def ComplexMeasurable {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop := ∃ (g: ℕ → EuclideanSpace' d → ℂ), (∀ n, ComplexSimpleFunction (g n)) ∧ (PointwiseConvergesTo g f)

def RealMeasurable {d:ℕ} (f: EuclideanSpace' d → ℝ) : Prop := ∃ (g: ℕ → EuclideanSpace' d → ℝ), (∀ n, RealSimpleFunction (g n)) ∧ (PointwiseConvergesTo g f)

