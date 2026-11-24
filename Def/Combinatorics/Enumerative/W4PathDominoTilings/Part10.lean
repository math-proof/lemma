module
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Nat.Fib.Basic
public import Def.NumberTheory.PellNumberSequence
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.W4PathDominoTilings.Part7
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/
section

namespace MetaMathlibExt

def HorizProps (f : Fin 4 → Fin 4) (U : Finset (Fin 4)) : Prop :=
  (∀ a ∈ U, f a ∈ U ∧ f (f a) = a ∧ f a ≠ a ∧ W4.Adj a (f a)) ∧ ∀ a ∉ U, f a = a

end MetaMathlibExt
end
