import Mathlib
import Theorem.Analysis.Tools.ExistsUnique


/-- An alternate form of the axiom of unique choice.   -/
noncomputable def Subsingleton.choose {α: Sort*} [Subsingleton α] [hn: Nonempty α] : α := hn.some

