/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Graph/GraphMinor.lean -/


import Def.Combinatorics.Graph.GraphMinor
import Lemma.Finset.Graph.GraphMinor
import Abbrev.MathlibExtTest.Combinatorics.Graph.GraphMinor


namespace MathlibExtTest.Combinatorics.Graph.GraphMinor

-- The bundled finiteness witness is synthesized at construction (no `fin :=`
-- needed above), and the projection exposes it for downstream use.
example : Finite (MetaMathlibExt.FinGraph.V emptyBool) := emptyBool.fin

-- Deleting one vertex from the empty graph on `Bool` leaves the empty graph on `Unit`.
example : MetaMathlibExt.IsMinor emptyUnit emptyBool :=
  MetaMathlibExt.IsMinor.of_step <|
    MetaMathlibExt.MinorStep.deleteVertex emptyUnit emptyBool unitToTrue
      (by simp [emptyUnit, emptyBool]) false (by
        intro x
        cases x
        · constructor
          · rintro ⟨y, hy⟩
            cases y
            contradiction
          · intro h
            exact (h rfl).elim
        · constructor
          · intro _ h
            cases h
          · intro _
            exact ⟨(), rfl⟩)

-- Deleting the unique edge of the complete graph on `Bool` leaves the empty graph.
example : MetaMathlibExt.IsMinor emptyBool completeBool :=
  MetaMathlibExt.IsMinor.of_step <|
    MetaMathlibExt.MinorStep.deleteEdge emptyBool completeBool (Equiv.refl Bool)
      (by simp [emptyBool]) false true (by simp [completeBool])
      (by simp [emptyBool]) (by
        intro u v huv
        cases u <;> cases v
        · exfalso
          simp [completeBool] at huv
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · exfalso
          simp [completeBool] at huv)

-- Contracting the unique edge of the complete graph on `Bool` gives one vertex.
example : MetaMathlibExt.IsMinor emptyUnit completeBool :=
  MetaMathlibExt.IsMinor.of_step <|
    MetaMathlibExt.MinorStep.contractEdge emptyUnit completeBool (fun _ => ())
      (by intro u; cases u; exact ⟨false, rfl⟩)
      false true (by simp [completeBool]) (by intro h; cases h) rfl
      (by
        intro x y _
        cases x <;> cases y
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · exact Or.inl rfl)
      (by
        intro u v
        cases u
        cases v
        simp [emptyUnit])

end MathlibExtTest.Combinatorics.Graph.GraphMinor
