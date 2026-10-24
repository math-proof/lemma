/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/EndpointMapMultigraph.lean -/


import sympy.atlas.Combinatorics.EndpointMapMultigraph
import Lemma.Finset.EndpointMapMultigraph


namespace EndpointMapMultigraphTest

open EndpointMapMultigraph

/-- A loop is one incident edge but contributes two endpoint incidences to the degree. -/
example :
    incident (fun _ : Fin 1 => (0 : Fin 1)) (fun _ => 0) 0 {0} = {0} ∧
      degreeWithin (fun _ : Fin 1 => (0 : Fin 1)) (fun _ => 0) {0} 0 = 2 := by
  constructor
  · ext e
    simp
  · exact degreeWithin_singleton_loop _ _ 0 rfl

/-- Two parallel loopless edges retain separate identities and form degree two at each end. -/
example :
    degreeWithin (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1) Finset.univ 0 = 2 ∧
      degreeWithin (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1) Finset.univ 1 = 2 := by
  constructor
  · rw [degreeWithin_eq_card_incident_of_loopless]
    · rw [show incident (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1) 0 Finset.univ =
          Finset.univ by ext e; simp]
      simp
    · simp
  · rw [degreeWithin_eq_card_incident_of_loopless]
    · rw [show incident (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1) 1 Finset.univ =
          Finset.univ by ext e; simp]
      simp
    · simp

/-- A loop does not cross a vertex cut. -/
example :
    cut (fun _ : Fin 1 => (0 : Fin 1)) (fun _ => 0) ({0} : Finset (Fin 1)) = ∅ := by
  ext e
  simp

/-- Cut membership is exactly endpoint-side disagreement. -/
example (end₁ end₂ : Fin 3 → Fin 2) (X : Finset (Fin 2)) (e : Fin 3) :
    e ∈ cut end₁ end₂ X ↔ (end₁ e ∈ X) ≠ (end₂ e ∈ X) := by
  simp

/-- Endpoint order does not affect the incidence and degree APIs. -/
example (end₁ end₂ : Fin 3 → Fin 2) (F : Finset (Fin 3)) (v : Fin 2) :
    incident end₂ end₁ v F = incident end₁ end₂ v F ∧
      degreeWithin end₂ end₁ F v = degreeWithin end₁ end₂ F v :=
  ⟨incident_swap _ _ _ _, degreeWithin_swap _ _ _ _⟩

/-- Endpoint order also leaves support, adjacency, cuts, connectivity, and
circuit structure unchanged. -/
example (end₁ end₂ : Fin 3 → Fin 2) (F : Finset (Fin 3)) (X : Finset (Fin 2))
    (u v : Fin 2) :
    support end₂ end₁ F = support end₁ end₂ F ∧
      (AdjacentUsing end₂ end₁ F u v ↔ AdjacentUsing end₁ end₂ F u v) ∧
      cut end₂ end₁ X = cut end₁ end₂ X ∧
      (IsConnectedOnSupport end₂ end₁ F ↔ IsConnectedOnSupport end₁ end₂ F) ∧
      (IsCircuit end₂ end₁ F ↔ IsCircuit end₁ end₂ F) := by
  exact ⟨support_swap _ _ _, adjacentUsing_swap _ _ _ _ _, cut_swap _ _ _,
    isConnectedOnSupport_swap _ _ _, isCircuit_swap _ _ _⟩

/-- Empty edge sets are connected on their empty support but are not circuits. -/
example (end₁ end₂ : Fin 1 → Fin 1) :
    IsConnectedOnSupport end₁ end₂ ∅ ∧ ¬IsCircuit end₁ end₂ ∅ := by
  simp

end EndpointMapMultigraphTest
