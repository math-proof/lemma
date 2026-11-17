module

public import Mathlib
public import Theorem.Analysis.Tools.ExistsUnique

@[expose] public section

/-- An alternate form of the axiom of unique choice.   -/
noncomputable def Subsingleton.choose {α: Sort*} [Subsingleton α] [hn: Nonempty α] : α := hn.some

