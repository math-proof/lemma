import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostdictionary
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc10_ghostEdge_coupling_eq_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostdictionary.lean)
-/
@[path]
private lemma gc10_ghostEdge_coupling_eq_field_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
-- given
  (h β : ℝ) :
-- imply
  ghostCoupling h β (fun _ => 1) s(some x, none) = h := by
-- proof
  apply StatMech.Walls.gc10_ghostEdge_coupling_eq_field G h β x

/--
[gc10_ghost_bondSum_absorbs_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostdictionary.lean)
-/
@[path]
private lemma gc10_ghost_bondSum_absorbs_field_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace (Option V)}
-- given
  (β h : ℝ) :
-- imply
  (∑ e ∈ (withGhost G).edgeFinset, ghostCoupling h β (fun _ => 1) e * bond s e) = (∑ e ∈ G.edgeFinset, (fun _ : Sym2 V => (1 : ℝ)) e * bond s (Sym2.map some e)) + h * spin s none * ∑ x : V, spin s (some x) := by
-- proof
  apply StatMech.Walls.gc10_ghost_bondSum_absorbs_field G β h s

/--
[gc10_ghostEdge_encodes_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostdictionary.lean)
-/
@[path]
private lemma gc10_ghostEdge_encodes_field_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace (Option V)}
-- given
  (β h : ℝ) :
-- imply
  boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) s = isingWeight G β (h * spin s none) (fun z => s (some z)) := by
-- proof
  apply StatMech.Walls.gc10_ghostEdge_encodes_field G β h s

/--
[gc10_ghostPaired_card_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostdictionary.lean)
-/
@[path]
private lemma gc10_ghostPaired_card_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (hA : Odd A.card) :
-- imply
  Even ((insert (none : Option V) (A.map someEmb)).card) := by
-- proof
  apply StatMech.Walls.gc10_ghostPaired_card_even G A hA

/--
[gc10_ghostPaired_observable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostdictionary.lean)
-/
@[path]
private lemma gc10_ghostPaired_observable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a : V}
  {s : ConfigSpace (Option V)} :
-- imply
  spinProd (insert (none : Option V) (({a} : Finset V).map someEmb)) s = spin s (some a) * spin s none := by
-- proof
  apply StatMech.Walls.gc10_ghostPaired_observable G a s

/--
[gc10_magnetisation_dictionary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostdictionary.lean)
-/
@[path]
private lemma gc10_magnetisation_dictionary_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a : V}
-- given
  (β h : ℝ) :
-- imply
  expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({a} : Finset V).map someEmb)) = isingExpectation G β h (fun s => spin s a) := by
-- proof
  apply StatMech.Walls.gc10_magnetisation_dictionary G β h a

/--
[gc10_magnetisation_dictionary_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostdictionary.lean)
-/
@[path]
private lemma gc10_magnetisation_dictionary_explicit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a : V}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => spin s a) = (∑ s : ConfigSpace (Option V), (spin s (some a) * spin s none) * boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) s) / partitionJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) := by
-- proof
  apply StatMech.Walls.gc10_magnetisation_dictionary_explicit G β h a

/--
[gc10_magnetisation_dictionary_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostdictionary.lean)
-/
@[path]
private lemma gc10_magnetisation_dictionary_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hA : Odd A.card) :
-- imply
  expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (A.map someEmb)) = isingExpectation G β h (spinProd A) := by
-- proof
  apply StatMech.Walls.gc10_magnetisation_dictionary_odd G β h A hA

/--
[gc10_ghost_Z0_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostdictionary.lean)
-/
@[path]
private lemma gc10_ghost_Z0_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  0 < currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc10_ghost_Z0_pos G β h

/--
[gc10_magnetisation_currentRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostdictionary.lean)
-/
@[path]
private lemma gc10_magnetisation_currentRatio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a : V}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => spin s a) = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({a} : Finset V).map someEmb)) / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc10_magnetisation_currentRatio G β h a

/--
[gc10_magnetisation_currentRatio_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostdictionary.lean)
-/
@[path]
private lemma gc10_magnetisation_currentRatio_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hA : Odd A.card) :
-- imply
  isingExpectation G β h (spinProd A) = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (A.map someEmb)) / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc10_magnetisation_currentRatio_odd G β h A hA

/--
[gc10_ghostDictionary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostdictionary.lean)
-/
@[path]
private lemma gc10_ghostDictionary_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a : V}
-- given
  (β h : ℝ) :
-- imply
  ((∀ x : V, ghostCoupling h β (fun _ => 1) s(some x, none) = h) ∧ (∀ s : ConfigSpace (Option V), boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) s = isingWeight G β (h * spin s none) (fun z => s (some z)))) ∧ (expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({a} : Finset V).map someEmb)) = isingExpectation G β h (fun s => spin s a)) ∧ (isingExpectation G β h (fun s => spin s a) = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({a} : Finset V).map someEmb)) / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ∧ (0 < currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) := by
-- proof
  apply StatMech.Walls.gc10_ghostDictionary G β h a

/--
[gc10_ghostDictionary_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostdictionary.lean)
-/
@[path]
private lemma gc10_ghostDictionary_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ((∀ x : Fin 3, ghostCoupling (1 : ℝ) 1 (fun _ => 1) s(some x, none) = 1) ∧ (∀ s : ConfigSpace (Option (Fin 3)), boltzmannJ (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) s = isingWeight (⊤ : SimpleGraph (Fin 3)) 1 (1 * spin s none) (fun z => s (some z)))) ∧ (expectationJ (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) (insert (none : Option (Fin 3)) (({0} : Finset (Fin 3)).map someEmb)) = isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (fun s => spin s 0)) ∧ (isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (fun s => spin s 0) = currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) (insert (none : Option (Fin 3)) (({0} : Finset (Fin 3)).map someEmb)) / currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅) ∧ (0 < currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅) := by
-- proof
  apply StatMech.Walls.gc10_ghostDictionary_nonvacuous G

/--
[gc10_ghostPaired_card_even_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostdictionary.lean)
-/
@[path]
private lemma gc10_ghostPaired_card_even_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Even ((insert (none : Option (Fin 3)) (({0} : Finset (Fin 3)).map someEmb)).card) := by
-- proof
  apply StatMech.Walls.gc10_ghostPaired_card_even_nonvacuous G


-- created on 2026-10-23
