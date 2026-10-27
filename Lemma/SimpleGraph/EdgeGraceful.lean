import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.SimpleGraph.EdgeGraceful
open scoped BigOperators
open SimpleGraph


namespace SimpleGraph

/--
[inducedResidue_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeGraceful.lean)
-/
@[path]
lemma inducedResidue_val
  [Fintype V]
  {G : SimpleGraph V}
  {q : Nat}
  {v : V}
-- given
  (label : G.edgeSet ≃ Fin q)
  (hp : Fintype.card V ≠ 0) :
-- imply
  (G.inducedResidue q label v).val =
    G.incidentSum q label v % Fintype.card V := by
-- proof
  classical
  unfold inducedResidue
  simp only [dite_eq_right hp]

end SimpleGraph

/--
[isEdgeGraceful_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeGraceful.lean)
-/
@[path]
lemma isEdgeGraceful_iff
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  G.IsEdgeGraceful ↔
    ∃ (q : Nat) (eLabel : G.edgeSet ≃ Fin q)
    (vLabel : V ≃ Fin (Fintype.card V)),
    ∀ v, vLabel v = G.inducedResidue q eLabel v ∧
    (Fintype.card V ≠ 0 →
    (vLabel v).val = G.incidentSum q eLabel v % Fintype.card V) := by
-- proof
  constructor
  · rintro ⟨q, eLabel, hbij⟩
    refine ⟨q, eLabel, Equiv.ofBijective _ hbij, fun v => ?_⟩
    constructor
    · rfl
    · intro hp
      exact G.inducedResidue_val q eLabel v hp
  · rintro ⟨q, eLabel, vLabel, h⟩
    refine ⟨q, eLabel, ?_⟩
    have h_eq : G.inducedResidue q eLabel = ⇑vLabel :=
      funext fun v => ((h v).1).symm
    rwa [h_eq]



-- created on 2026-10-20
-- updated on 2026-10-26
