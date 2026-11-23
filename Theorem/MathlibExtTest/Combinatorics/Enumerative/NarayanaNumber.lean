/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/NarayanaNumber.lean -/
module

public import Def.Combinatorics.Enumerative.NarayanaNumber
public import Theorem.Finset.Enumerative.NarayanaNumber

public section

namespace MetaMathlibExt

example : narayana ⟨1, by decide⟩ ⟨1, by decide⟩ = 1 := by decide

example : narayana ⟨3, by decide⟩ ⟨2, by decide⟩ = 3 := by decide

example : narayana ⟨3, by decide⟩ ⟨4, by decide⟩ = 0 := by decide

#print axioms narayana_eq_second

end MetaMathlibExt
