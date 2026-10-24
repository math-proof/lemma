/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/NarayanaNumber.lean -/


import sympy.atlas.Combinatorics.Enumerative.NarayanaNumber
import Lemma.Finset.Enumerative.NarayanaNumber

namespace MetaMathlibExt

example : narayana ⟨1, by decide⟩ ⟨1, by decide⟩ = 1 := by decide
example : narayana ⟨3, by decide⟩ ⟨2, by decide⟩ = 3 := by decide
example : narayana ⟨3, by decide⟩ ⟨4, by decide⟩ = 0 := by decide

#print axioms narayana_eq_second

end MetaMathlibExt
