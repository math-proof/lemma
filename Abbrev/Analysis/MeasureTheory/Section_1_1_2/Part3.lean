import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import Def.Analysis.MeasureTheory.Section_1_1_2
open Pointwise


/-- A set is Jordan null if it is Jordan measurable with measure zero. -/
abbrev JordanMeasurable.null {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop := ∃ hE: JordanMeasurable E, hE.measure = 0

/-- A dyadic box at scale 2^(-n) with multi-index i: the half-open cube \[i/2^n, (i+1)/2^n). -/
noncomputable abbrev Box.dyadic {d:ℕ} (n:ℤ) (i:Fin d → ℤ) : Box d where
  side j := BoundedInterval.Ico ((i j)/2^n) ((i j + 1)/2^n)

/-- Lower metric entropy: count of dyadic boxes at scale n fully contained in E. -/
noncomputable abbrev metric_entropy_lower {d:ℕ} (E: Set (EuclideanSpace' d)) (n:ℤ) : ℕ := Nat.card { i:Fin d → ℤ | (Box.dyadic n i).toSet ⊆ E }

/-- Upper metric entropy: count of dyadic boxes at scale n that intersect E. -/
noncomputable abbrev metric_entropy_upper {d:ℕ} (E: Set (EuclideanSpace' d)) (n:ℤ) : ℕ := Nat.card { i:Fin d → ℤ | (Box.dyadic n i).toSet ∩ E ≠ ∅ }

