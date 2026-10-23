import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2
open UnsignedMeasurable


/--
[UnsignedMeasurable.TFAE](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → EReal}
-- given
  (hf: Unsigned f) :
-- imply
  [
        UnsignedMeasurable f,
        ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (∀ x, Filter.atTop.Tendsto (fun n ↦ g n x) (nhds (f x))),
        ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (PointwiseAeConvergesTo g f),
        ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n) ∧  EReal.BoundedFunction (g n) ∧ FiniteMeasureSupport (g n)) ∧ (∀ x, Monotone (fun n ↦ g n x)) ∧ (∀ x, f x = iSup (fun n ↦ g n x)),
        ∀ t, LebesgueMeasurable {x | f x > t},
        ∀ t, LebesgueMeasurable {x | f x ≥ t},
        ∀ t, LebesgueMeasurable {x | f x < t},
        ∀ t, LebesgueMeasurable {x | f x ≤ t},
        ∀ I:BoundedInterval, LebesgueMeasurable (f⁻¹' (Real.toEReal '' I.toSet)),
        ∀ U: Set EReal, IsOpen U → LebesgueMeasurable (f⁻¹' U),
        ∀ K: Set EReal, IsClosed K → LebesgueMeasurable (f⁻¹' K)
      ].TFAE :=
-- proof
  UnsignedMeasurable.TFAE hf


-- created on 2026-10-22
