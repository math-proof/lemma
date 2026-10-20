/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeGraceful.lean -/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Edge-graceful labelings

This module defines edge-graceful labelings of finite simple graphs.

Reference: Lo's original definition as surveyed in https://arxiv.org/abs/2608.23881v1.

Main definitions:
* `SimpleGraph.incidentSum`: one-based incident-edge sum at a vertex.
* `SimpleGraph.inducedResidue`: induced vertex residue in `Fin (Fintype.card V)`.
* `SimpleGraph.IsEdgeGraceful`: existence of an edge bijection inducing a vertex bijection.
* `SimpleGraph.isEdgeGraceful_iff`: characterization via an explicit vertex bijection.
-/

open scoped BigOperators

namespace SimpleGraph

variable {V : Type*} [Fintype V]

/-- Incident-edge sum at `v`: finite labels `k : Fin q` contribute source
label `k.val + 1` when `v` lies in the corresponding edge. -/
noncomputable def incidentSum (G : SimpleGraph V) (q : Nat)
    (label : G.edgeSet ≃ Fin q) (v : V) : Nat := by
  classical
  exact ∑ k : Fin q, if v ∈ (label.symm k).val then (k.val + 1) else 0

/-- Induced vertex residue in `Fin (Fintype.card V)`. When the card is zero
there is no modulo to evaluate: map through `Fintype.equivFin V` and eliminate
the resulting `Fin 0`. Thus the empty graph gets the canonical empty vertex
bijection. -/
noncomputable def inducedResidue (G : SimpleGraph V) (q : Nat)
    (label : G.edgeSet ≃ Fin q) (v : V) : Fin (Fintype.card V) := by
  classical
  by_cases hp : Fintype.card V = 0
  · exact Fin.elim0 (cast (congrArg Fin hp) ((Fintype.equivFin V) v))
  · exact ⟨G.incidentSum q label v % Fintype.card V,
      Nat.mod_lt _ (Nat.pos_of_ne_zero hp)⟩

/-- Residue unfolds to the incident sum modulo `p` when `p ≠ 0`. -/
theorem inducedResidue_val (G : SimpleGraph V) (q : Nat)
    (label : G.edgeSet ≃ Fin q) (v : V) (hp : Fintype.card V ≠ 0) :
    (G.inducedResidue q label v).val =
      G.incidentSum q label v % Fintype.card V := by
  classical
  unfold inducedResidue
  simp only [dite_eq_right hp]

/-- Edge-graceful: some edge-bijection with `Fin q` induces a bijective
vertex-residue map. Only `[Fintype V]` is assumed publicly. -/
def IsEdgeGraceful (G : SimpleGraph V) : Prop :=
  ∃ (q : Nat) (label : G.edgeSet ≃ Fin q),
    Function.Bijective (G.inducedResidue q label)

/-- Characterization exposing existence, edge-bijection, incident-sum and
vertex-bijection clauses. -/
theorem isEdgeGraceful_iff (G : SimpleGraph V) :
    G.IsEdgeGraceful ↔
      ∃ (q : Nat) (eLabel : G.edgeSet ≃ Fin q)
        (vLabel : V ≃ Fin (Fintype.card V)),
        ∀ v, vLabel v = G.inducedResidue q eLabel v ∧
          (Fintype.card V ≠ 0 →
            (vLabel v).val = G.incidentSum q eLabel v % Fintype.card V) := by
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
    rw [h_eq]
    exact vLabel.bijective

end SimpleGraph
