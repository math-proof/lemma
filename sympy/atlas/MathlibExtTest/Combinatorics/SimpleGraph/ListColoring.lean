/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/ListColoring.lean -/


import sympy.atlas.Combinatorics.SimpleGraph.ListColoring
import Lemma.SimpleGraph.ListColoring


open SimpleGraph

/-- The one-vertex graph has choice number one, including the zero boundary. -/
example : (⊥ : SimpleGraph (Fin 1)).IsChoiceNumber 1 := by
  refine ⟨finOne_isListColorable, ?_⟩
  intro q hq
  have hq0 : q = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hq)
  subst q
  intro hzero
  obtain ⟨color, _⟩ := hzero Empty (fun _ => ∅) (by simp)
  exact (color 0).elim

/-- Requiring larger lists preserves list colorability. -/
example {V : Type*} (G : SimpleGraph V) (hG : G.IsListColorable 2) :
    G.IsListColorable 3 :=
  hG.mono (by decide)

/-- The shared notion specializes to ordinary Mathlib vertex colorability. -/
example {V : Type*} (G : SimpleGraph V) (q : ℕ) (hG : G.IsListColorable q) :
    G.Colorable q :=
  hG.colorable
