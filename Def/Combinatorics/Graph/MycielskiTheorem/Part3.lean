/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.CharP.Defs
import Mathlib.Order.CompletePartialOrder
import Theorem.Combinatorics.Graph.MycielskiTheorem.Part2


namespace MetaMathlibExt

open scoped SimpleGraph

def myCopy {V : Type*} (G : SimpleGraph V) : G.Copy (myGraph G) where
  toHom := ⟨fun v => some (v, false), fun h => myAdj_of00 h⟩
  injective' := by
    intro a b h
    have h2 : some (a, false) = some (b, false) := h
    exact congrArg Prod.fst (Option.some_inj.mp h2)

def myRawColor {V : Type*} {k : ℕ} (d : Option (V × Bool) → Fin (k + 1))
    (j : Fin (k + 1)) (v : V) : Fin (k + 1) :=
  if d (some (v, false)) = j then d (some (v, true)) else d (some (v, false))

end MetaMathlibExt
