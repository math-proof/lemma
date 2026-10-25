/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Words/KolakoskiSequence.lean -/


import Def.Combinatorics.Words.KolakoskiSequence
import Lemma.Finset.Words.KolakoskiSequence


namespace MetaMathlibExt

example (K : ℕ → ℕ) (h : IsKolakoski K) :
    K 1 = 1 ∧ K 2 = 2 ∧ K 3 = 2 ∧ K 4 = 1 :=
  ⟨h.one, h.two, h.three, h.four⟩

#print axioms kolakoskiBlockStart
#print axioms IsKolakoski
#print axioms IsKolakoski.two
#print axioms IsKolakoski.three
#print axioms IsKolakoski.four

end MetaMathlibExt
