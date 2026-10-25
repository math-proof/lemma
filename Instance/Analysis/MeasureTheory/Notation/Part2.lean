import Mathlib
import Theorem.Analysis.MeasureTheory.Notation.Part4
open Filter


noncomputable instance EReal.inst_posPart : PosPart EReal where
  posPart := fun x ↦ if x ≥ 0 then x else 0

noncomputable instance EReal.inst_negPart : NegPart EReal where
  negPart := fun x ↦ if x ≤ 0 then -x else 0

