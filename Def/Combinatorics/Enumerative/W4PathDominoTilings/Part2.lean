/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

module

public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Nat.Fib.Basic
public import Def.NumberTheory.PellNumberSequence
public import Mathlib.Tactic.Ring
public import Instance.Combinatorics.Enumerative.W4PathDominoTilings

@[expose] public section

open SimpleGraph


section

namespace MetaMathlibExt

-- Horizontal matchings on `U ⊆ Fin 4`: fixed-point-free involutions using `W4`-edges.
def HorizPairing (U : Finset (Fin 4)) : Type :=
  { f : Fin 4 → Fin 4 //
    (∀ a ∈ U, f a ∈ U ∧ f (f a) = a ∧ f a ≠ a ∧ W4.Adj a (f a)) ∧
    ∀ a ∉ U, f a = a }

end MetaMathlibExt
end
