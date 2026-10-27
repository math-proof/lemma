import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc6_ghostgraph
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc6_num_neg_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_ghostgraph.lean)
-/
@[path]
private lemma gc6_num_neg_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hA : Odd A.card) :
-- imply
  (∑ s : ConfigSpace V, spinProd A s * isingWeight G β (-h) s) = - ∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s := by
-- proof
  apply StatMech.Walls.gc6_num_neg_odd G β h A hA

/--
[gc6_spinProd_insert_ghost_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_ghostgraph.lean)
-/
@[path]
private lemma gc6_spinProd_insert_ghost_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {s : ConfigSpace (Option V)} :
-- imply
  spinProd (insert (none : Option V) (A.map someEmb)) s = spin s none * spinProd (A.map someEmb) s := by
-- proof
  apply StatMech.Walls.gc6_spinProd_insert_ghost_factor G A s

/--
[gc6_spinProd_insert_ghost_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_ghostgraph.lean)
-/
@[path]
private lemma gc6_spinProd_insert_ghost_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {b : Bool}
  {τ : V → Bool} :
-- imply
  spinProd (insert (none : Option V) (A.map someEmb)) (fun a => Option.rec b τ a : Option V → Bool) = StatMech.Ising.spinB b * spinProd A τ := by
-- proof
  apply StatMech.Walls.gc6_spinProd_insert_ghost_split G A b τ

/--
[gc6_num_ghost_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_ghostgraph.lean)
-/
@[path]
private lemma gc6_num_ghost_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hA : Odd A.card) :
-- imply
  (∑ s : ConfigSpace (Option V), spinProd (insert (none : Option V) (A.map someEmb)) s * boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) s) = 2 * ∑ τ : ConfigSpace V, spinProd A τ * isingWeight G β h τ := by
-- proof
  apply StatMech.Walls.gc6_num_ghost_odd G β h A hA

/--
[gc6_expectationJ_ghost_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_ghostgraph.lean)
-/
@[path]
private lemma gc6_expectationJ_ghost_odd_eq
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
  apply StatMech.Walls.gc6_expectationJ_ghost_odd G β h A hA

/--
[gc6_ghostGraph_dictionary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_ghostgraph.lean)
-/
@[path]
private lemma gc6_ghostGraph_dictionary_eq
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
  apply StatMech.Walls.gc6_ghostGraph_dictionary G β h a

/--
[gc6_ghostGraph_dictionary_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_ghostgraph.lean)
-/
@[path]
private lemma gc6_ghostGraph_dictionary_explicit_eq
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
  apply StatMech.Walls.gc6_ghostGraph_dictionary_explicit G β h a

/--
[gc6_ghostGraph_currentRatio_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_ghostgraph.lean)
-/
@[path]
private lemma gc6_ghostGraph_currentRatio_odd_eq
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
  apply StatMech.Walls.gc6_ghostGraph_currentRatio_odd G β h A hA

/--
[gc6_ghostGraph_currentRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_ghostgraph.lean)
-/
@[path]
private lemma gc6_ghostGraph_currentRatio_eq
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
  apply StatMech.Walls.gc6_ghostGraph_currentRatio G β h a

/--
[gc6_ghost_Z0_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_ghostgraph.lean)
-/
@[path]
private lemma gc6_ghost_Z0_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  0 < currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc6_ghost_Z0_pos G β h

/--
[gc6_ergRep_ghost_compat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_ghostgraph.lean)
-/
@[path]
private lemma gc6_ergRep_ghost_compat_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a : V}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => spin s a) = Sharpness.expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({a} : Finset V).map someEmb)) := by
-- proof
  apply StatMech.Walls.gc6_ergRep_ghost_compat G β h a

/--
[gc6_ghostGraph_dictionary_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_ghostgraph.lean)
-/
@[path]
private lemma gc6_ghostGraph_dictionary_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  expectationJ (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) (insert (none : Option (Fin 3)) (({0} : Finset (Fin 3)).map someEmb)) = isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (fun s => spin s 0) := by
-- proof
  apply StatMech.Walls.gc6_ghostGraph_dictionary_nonvacuous G

/--
[gc6_ghostGraph_currentRatio_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_ghostgraph.lean)
-/
@[path]
private lemma gc6_ghostGraph_currentRatio_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (fun s => spin s 0) = currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) (insert (none : Option (Fin 3)) (({0} : Finset (Fin 3)).map someEmb)) / currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc6_ghostGraph_currentRatio_nonvacuous G


-- created on 2026-10-23
