/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Graph/GraphMinor.lean -/


import sympy.atlas.Combinatorics.Graph.GraphMinor
import Lemma.Finset.Graph.GraphMinor


namespace MathlibExtTest.Combinatorics.Graph.GraphMinor

#check MetaMathlibExt.FinGraph
#check MetaMathlibExt.MinorStep
#check MetaMathlibExt.IsMinor

-- Reflexivity: every graph is a minor of itself.
example (G : MetaMathlibExt.FinGraph) : MetaMathlibExt.IsMinor G G :=
  MetaMathlibExt.IsMinor.refl G

-- Transitivity through an intermediate minor.
example {H K G : MetaMathlibExt.FinGraph} :
    MetaMathlibExt.IsMinor H K → MetaMathlibExt.IsMinor K G →
      MetaMathlibExt.IsMinor H G :=
  MetaMathlibExt.IsMinor.trans

-- The identity relabelling is a one-step isomorphism minor.
example (G : MetaMathlibExt.FinGraph) : MetaMathlibExt.IsMinor G G :=
  MetaMathlibExt.IsMinor.of_iso .refl

private abbrev emptyBool : MetaMathlibExt.FinGraph where
  V := Bool
  G := ⊥

private abbrev completeBool : MetaMathlibExt.FinGraph where
  V := Bool
  G := ⊤

private abbrev emptyUnit : MetaMathlibExt.FinGraph where
  V := Unit
  G := ⊥

private abbrev unitToTrue : Unit ↪ Bool where
  toFun _ := true
  inj' _ _ _ := Subsingleton.elim _ _

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
