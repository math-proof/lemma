import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Def.Analysis.MeasureTheory.Section_1_3_2
set_option doc.verso.suggestions false


namespace UnsignedMeasurable.TFAE_helpers

variable {d : ℕ} {f : EuclideanSpace' d → EReal}

-- Statement abbreviations for clarity (using indices as in the book)
private abbrev stmt_i (f : EuclideanSpace' d → EReal) := UnsignedMeasurable f

private abbrev stmt_ii (f : EuclideanSpace' d → EReal) :=
  ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (∀ x, Filter.atTop.Tendsto (fun n ↦ g n x) (nhds (f x)))

private abbrev stmt_iii (f : EuclideanSpace' d → EReal) :=
  ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (PointwiseAeConvergesTo g f)

private abbrev stmt_iv (f : EuclideanSpace' d → EReal) :=
  ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n) ∧ EReal.BoundedFunction (g n) ∧ FiniteMeasureSupport (g n)) ∧ (∀ x, Monotone (fun n ↦ g n x)) ∧ (∀ x, f x = iSup (fun n ↦ g n x))

private abbrev stmt_v (f : EuclideanSpace' d → EReal) := ∀ t, LebesgueMeasurable {x | f x > t}

private abbrev stmt_vi (f : EuclideanSpace' d → EReal) := ∀ t, LebesgueMeasurable {x | f x ≥ t}

private abbrev stmt_vii (f : EuclideanSpace' d → EReal) := ∀ t, LebesgueMeasurable {x | f x < t}

private abbrev stmt_viii (f : EuclideanSpace' d → EReal) := ∀ t, LebesgueMeasurable {x | f x ≤ t}

private abbrev stmt_ix (f : EuclideanSpace' d → EReal) := ∀ I:BoundedInterval, LebesgueMeasurable (f⁻¹' (Real.toEReal '' I.toSet))

private abbrev stmt_x (f : EuclideanSpace' d → EReal) := ∀ U: Set EReal, IsOpen U → LebesgueMeasurable (f⁻¹' U)

private abbrev stmt_xi (f : EuclideanSpace' d → EReal) := ∀ K: Set EReal, IsClosed K → LebesgueMeasurable (f⁻¹' K)

end UnsignedMeasurable.TFAE_helpers
