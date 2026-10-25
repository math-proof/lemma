/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.CharP.Defs
import Mathlib.Order.CompletePartialOrder
import Theorem.Combinatorics.Graph.MycielskiTheorem.Part3


namespace MetaMathlibExt

open scoped SimpleGraph

def mapGraph {A : Type*} {B : Type*} (e : A ≃ B) (G : SimpleGraph A) : SimpleGraph B where
  Adj a b := G.Adj (e.symm a) (e.symm b)
  symm := ⟨fun _ _ h => G.symm.symm _ _ h⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h⟩

def isoMap {A : Type*} {B : Type*} (e : A ≃ B) (G : SimpleGraph A) :
    G ≃g mapGraph e G :=
  ⟨e, fun {a b} => by
    change G.Adj (e.symm (e a)) (e.symm (e b)) ↔ G.Adj a b
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]⟩

def copyOfIso {V : Type*} {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) : G.Copy H :=
  SimpleGraph.Copy.mk ⟨f.toEquiv.toFun, fun h => f.map_rel_iff'.mpr h⟩ f.toEquiv.injective

end MetaMathlibExt
