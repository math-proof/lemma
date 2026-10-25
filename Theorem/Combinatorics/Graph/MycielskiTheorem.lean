/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.CharP.Defs
import Mathlib.Order.CompletePartialOrder
import Def.Combinatorics.Graph.MycielskiTheorem


namespace MetaMathlibExt

open scoped SimpleGraph

theorem myAdj_symm {V : Type*} (G : SimpleGraph V) : Std.Symm (myAdj G) :=
  ⟨fun x y h => by
    simp only [myAdj] at h ⊢
    rcases h with ⟨v, u, rfl, rfl, h⟩ | ⟨v, u, rfl, rfl, h⟩ | ⟨v, u, rfl, rfl, h⟩ |
      ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩
    · exact Or.inl ⟨u, v, rfl, rfl, G.symm.symm _ _ h⟩
    · exact Or.inr (Or.inr (Or.inl ⟨u, v, rfl, rfl, G.symm.symm _ _ h⟩))
    · exact Or.inr (Or.inl ⟨u, v, rfl, rfl, G.symm.symm _ _ h⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨v, rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl, rfl⟩)))⟩

theorem myAdj_irrefl {V : Type*} (G : SimpleGraph V) : Std.Irrefl (myAdj G) :=
  ⟨fun x h => by
    simp only [myAdj] at h
    rcases h with ⟨v, u, hx1, hx2, hadj⟩ | ⟨v, u, hx1, hx2, hadj⟩ | ⟨v, u, hx1, hx2, hadj⟩ |
      ⟨v, hx1, hx2⟩ | ⟨v, hx1, hx2⟩
    · have huv : v = u := congrArg Prod.fst (Option.some_inj.mp (hx1.symm.trans hx2))
      subst huv
      exact G.loopless.irrefl _ hadj
    · have huv : v = u := congrArg Prod.fst (Option.some_inj.mp (hx1.symm.trans hx2))
      subst huv
      exact G.loopless.irrefl _ hadj
    · have huv : v = u := congrArg Prod.fst (Option.some_inj.mp (hx1.symm.trans hx2))
      subst huv
      exact G.loopless.irrefl _ hadj
    · exact (Option.some_ne_none _ (hx1.symm.trans hx2)).elim
    · exact (Option.some_ne_none _ (hx2.symm.trans hx1)).elim⟩

end MetaMathlibExt
