/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Square.lean -/


import Mathlib.Combinatorics.SimpleGraph.Hasse
import Theorem.Combinatorics.SimpleGraph.Square
import Lemma.SimpleGraph.Square
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.Square


namespace MathlibExtTest.Combinatorics.SimpleGraph.Square

noncomputable local instance : DecidableRel (⊤ : SimpleGraph (Fin 5)).square.Adj :=
  fun _ _ ↦ Classical.propDecidable _

end MathlibExtTest.Combinatorics.SimpleGraph.Square
