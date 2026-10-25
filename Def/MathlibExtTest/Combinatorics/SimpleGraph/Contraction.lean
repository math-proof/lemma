/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Contraction.lean -/


import Theorem.Combinatorics.SimpleGraph.Contraction.Part3
import Lemma.SimpleGraph.Contraction
import Abbrev.MathlibExtTest.Combinatorics.SimpleGraph.Contraction


namespace MathlibExtTest.Combinatorics.SimpleGraph.Contraction

def zero : retained := ⟨0, by simp [retained]⟩

def one : retained := ⟨1, by simp [retained]⟩

end MathlibExtTest.Combinatorics.SimpleGraph.Contraction
