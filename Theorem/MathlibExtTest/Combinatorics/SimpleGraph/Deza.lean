/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Deza.lean -/


import Mathlib.Tactic.FinCases
import Structure.Combinatorics.SimpleGraph.Deza
import Lemma.SimpleGraph.Deza
open SimpleGraph


/-- The triangle is Deza with parameters `(3, 2, 1, 1)`. -/
example : (⊤ : SimpleGraph (Fin 3)).IsDezaWith 3 2 1 1 := by
  refine IsDezaWith.mk (G := (⊤ : SimpleGraph (Fin 3))) ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · intro v
    fin_cases v <;> decide
  · decide

/-- The edgeless graph on three vertices is Deza with `(3, 0, 0, 0)`. -/
example : (⊥ : SimpleGraph (Fin 3)).IsDezaWith 3 0 0 0 := by
  refine IsDezaWith.mk (G := (⊥ : SimpleGraph (Fin 3))) ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · intro v
    fin_cases v <;> decide
  · decide

/-- The triangle also satisfies the two-valued clause for `(3, 2, 2, 1)`. -/
example : (⊤ : SimpleGraph (Fin 3)).IsDezaWith 3 2 2 1 := by
  refine IsDezaWith.mk (G := (⊤ : SimpleGraph (Fin 3))) ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · intro v
    fin_cases v <;> decide
  · decide

/-- Vertex-count mismatch: the cardinality clause is the only failure. -/
example : ¬ (⊤ : SimpleGraph (Fin 3)).IsDezaWith 4 2 1 1 := by
  intro h
  exact absurd h.card_eq (by decide)

/-- Regularity is the only failing clause: all shared counts are `0`. -/
example : ¬ (⊥ : SimpleGraph (Fin 3)).IsDezaWith 3 1 0 0 := by
  intro h
  have hreg : ∀ v : Fin 3, (⊥ : SimpleGraph (Fin 3)).degree v = 1 := h.regular
  have h0 : (⊥ : SimpleGraph (Fin 3)).degree (0 : Fin 3) = 1 := hreg _
  exact absurd h0 (by decide)

/-- The two-valued clause is the only failing clause: the graph is `2`-regular. -/
example : ¬ (⊤ : SimpleGraph (Fin 3)).IsDezaWith 3 2 0 0 := by
  intro h
  have hc := h.common_eq (u := (0 : Fin 3)) (v := (1 : Fin 3)) (by decide)
  revert hc
  decide

/-- Parameter order matters: the counts fit the set but `a ≤ b` fails. -/
example : ¬ (⊤ : SimpleGraph (Fin 3)).IsDezaWith 3 2 0 1 := by
  intro h
  exact absurd h.a_le_b (by decide)

/-- Projections recover regularity. -/
example (h : (⊤ : SimpleGraph (Fin 3)).IsDezaWith 3 2 1 1) :
    (⊤ : SimpleGraph (Fin 3)).IsRegularOfDegree 2 :=
  h.regular

/-- Projections recover the vertex count. -/
example (h : (⊥ : SimpleGraph (Fin 3)).IsDezaWith 3 0 0 0) :
    Fintype.card (Fin 3) = 3 :=
  h.card_eq

