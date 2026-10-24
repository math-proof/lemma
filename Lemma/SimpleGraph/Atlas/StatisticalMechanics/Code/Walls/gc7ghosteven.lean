import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc7ghosteven
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc7_edge_card_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7ghosteven.lean)
-/
@[path]
private lemma gc7_edge_card_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V}
-- given
  (he : e ∈ G.edgeFinset) :
-- imply
  #(Finset.univ.filter (fun x : V => x ∈ e)) = 2 := by
-- proof
  apply StatMech.Walls.gc7_edge_card_two G e he

/--
[gc7_sum_incidentFlux_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7ghosteven.lean)
-/
@[path]
private lemma gc7_sum_incidentFlux_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Sharpness.Current V} :
-- imply
  Even (∑ x : V, Sharpness.incidentFlux G n x) := by
-- proof
  apply StatMech.Walls.gc7_sum_incidentFlux_even G n

/--
[gc7_sources_card_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7ghosteven.lean)
-/
@[path]
private lemma gc7_sources_card_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Sharpness.Current V} :
-- imply
  Even (sources G n).card := by
-- proof
  apply StatMech.Walls.gc7_sources_card_even G n

/--
[gc7_triple_card_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7ghosteven.lean)
-/
@[path]
private lemma gc7_triple_card_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  Odd (({o, x, y} : Finset V).card) := by
-- proof
  apply StatMech.Walls.gc7_triple_card_odd G o x y hox hoy hxy

/--
[gc7_combined_source_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7ghosteven.lean)
-/
@[path]
private lemma gc7_combined_source_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card = 4 := by
-- proof
  apply StatMech.Walls.gc7_combined_source_card G o x y hox hoy hxy

/--
[gc7_combined_source_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7ghosteven.lean)
-/
@[path]
private lemma gc7_combined_source_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  Even (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card := by
-- proof
  apply StatMech.Walls.gc7_combined_source_even G o x y hox hoy hxy

/--
[gc7_ghostEven_dictionary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7ghosteven.lean)
-/
@[path]
private lemma gc7_ghostEven_dictionary_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  isingExpectation G β h (spinProd ({o, x, y} : Finset V)) = expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) := by
-- proof
  apply StatMech.Walls.gc7_ghostEven_dictionary G β h o x y hox hoy hxy

/--
[gc7_ghostEven_currentRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7ghosteven.lean)
-/
@[path]
private lemma gc7_ghostEven_currentRatio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  isingExpectation G β h (spinProd ({o, x, y} : Finset V)) = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc7_ghostEven_currentRatio G β h o x y hox hoy hxy

/--
[gc7_representing_current_sources_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7ghosteven.lean)
-/
@[path]
private lemma gc7_representing_current_sources_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Sharpness.Current (Option V)}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hm : sources (withGhost G) m = insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) :
-- imply
  Even (sources (withGhost G) m).card ∧ Even (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card := by
-- proof
  apply StatMech.Walls.gc7_representing_current_sources_even G m o x y hox hoy hxy hm

/--
[gc7_ghostEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7ghosteven.lean)
-/
@[path]
private lemma gc7_ghostEven_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  Even (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card ∧ isingExpectation G β h (spinProd ({o, x, y} : Finset V)) = expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∧ isingExpectation G β h (spinProd ({o, x, y} : Finset V)) = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc7_ghostEven G β h o x y hox hoy hxy

/--
[gc7_combined_source_even_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7ghosteven.lean)
-/
@[path]
private lemma gc7_combined_source_even_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Even (insert (none : Option (Fin 3)) (({0, 1, 2} : Finset (Fin 3)).map someEmb)).card := by
-- proof
  apply StatMech.Walls.gc7_combined_source_even_nonvacuous G

/--
[gc7_ghostEven_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7ghosteven.lean)
-/
@[path]
private lemma gc7_ghostEven_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Even (insert (none : Option (Fin 3)) (({0, 1, 2} : Finset (Fin 3)).map someEmb)).card ∧ isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1, 2} : Finset (Fin 3))) = expectationJ (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) (insert (none : Option (Fin 3)) (({0, 1, 2} : Finset (Fin 3)).map someEmb)) ∧ isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1, 2} : Finset (Fin 3))) = currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) (insert (none : Option (Fin 3)) (({0, 1, 2} : Finset (Fin 3)).map someEmb)) / currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc7_ghostEven_nonvacuous G


-- created on 2026-10-23
