/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.W4PathDominoTilings.Part7
open SimpleGraph


section

namespace MetaMathlibExt

def HorizProps (f : Fin 4 → Fin 4) (U : Finset (Fin 4)) : Prop :=
  (∀ a ∈ U, f a ∈ U ∧ f (f a) = a ∧ f a ≠ a ∧ W4.Adj a (f a)) ∧ ∀ a ∉ U, f a = a

end MetaMathlibExt
end
