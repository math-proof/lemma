/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/OddIndependent.lean -/
module

public import Def.Combinatorics.SimpleGraph.OddIndependent
public import Theorem.SimpleGraph.OddIndependent
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Odd independent set tests

Checks the empty/singleton theorems and separates independence from the
parity condition on the three-vertex path.
-/

public section


/-- Empty and singleton sanity checks for odd independence. -/
example : (SimpleGraph.pathGraph 3).IsOddIndependent ∅ :=
  (SimpleGraph.pathGraph 3).isOddIndependent_empty

example (a : Fin 3) : (SimpleGraph.pathGraph 3).IsOddIndependent {a} :=
  (SimpleGraph.pathGraph 3).isOddIndependent_singleton a

