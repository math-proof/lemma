module
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Theorem.Combinatorics.SimpleGraph.Square
public import Theorem.SimpleGraph.Square
public import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.Square


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Square.lean -/
namespace MathlibExtTest.Combinatorics.SimpleGraph.Square

noncomputable local instance : DecidableRel (⊤ : SimpleGraph (Fin 5)).square.Adj :=
  fun _ _ ↦ Classical.propDecidable _

end MathlibExtTest.Combinatorics.SimpleGraph.Square
