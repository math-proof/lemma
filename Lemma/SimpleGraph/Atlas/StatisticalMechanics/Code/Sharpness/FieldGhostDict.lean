import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
open Finset SimpleGraph StatMech StatMech.Ising StatMech.Sharpness StatMech.Sharpness.FieldGhostDict


/--
[withGhost_edgeFinset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma withGhost_edgeFinset_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  (withGhost G).edgeFinset = origEdges G ∪ ghostEdges V := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.withGhost_edgeFinset_eq G

/--
[disjoint_orig_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma disjoint_orig_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Disjoint (origEdges G) (ghostEdges V) := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.disjoint_orig_ghost G

/--
[ghostCoupling_some_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma ghostCoupling_some_some_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {x y : V}
-- given
  (h β : ℝ) :
-- imply
  ghostCoupling h β J s(some x, some y) = J s(x, y) := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.ghostCoupling_some_some G h β J x y

/--
[ghostCoupling_some_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma ghostCoupling_some_none_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {x : V}
-- given
  (h β : ℝ) :
-- imply
  ghostCoupling h β J s(some x, none) = h := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.ghostCoupling_some_none G h β J x

/--
[bond_map_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma bond_map_some_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace (Option V)}
  {e : Sym2 V} :
-- imply
  bond s (Sym2.map some e) = bond (fun x => s (some x)) e := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.bond_map_some G s e

/--
[ghost_bondSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma ghost_bondSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {s : ConfigSpace (Option V)}
-- given
  (h β : ℝ) :
-- imply
  (∑ e ∈ (withGhost G).edgeFinset, ghostCoupling h β J e * bond s e) = (∑ e ∈ G.edgeFinset, J e * bond s (Sym2.map some e)) + h * spin s none * ∑ x : V, spin s (some x) := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.ghost_bondSum G h β J s

/--
[fgd_ghost_weight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma fgd_ghost_weight_eq_eq
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
  apply StatMech.Sharpness.FieldGhostDict.fgd_ghost_weight_eq G β h s

/--
[flipV_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma flipV_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
  {v : V} :
-- imply
  flipV s v = ! s v := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.flipV_apply G s v

/--
[spin_flipV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma spin_flipV_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
  {v : V} :
-- imply
  spin (flipV s) v = - spin s v := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.spin_flipV G s v

/--
[bond_flipV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma bond_flipV_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  bond (flipV s) e = bond s e := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.bond_flipV G s e

/--
[flipV_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma flipV_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Function.Involutive (flipV (V := V)) := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.flipV_involutive G

/--
[isingWeight_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma isingWeight_flip_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  isingWeight G β (-h) (flipV s) = isingWeight G β h s := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.isingWeight_flip G β h s

/--
[fgd_isingZ_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma fgd_isingZ_neg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  isingZ G β (-h) = isingZ G β h := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.fgd_isingZ_neg G β h

/--
[spinProd_flipV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma spinProd_flipV_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {s : ConfigSpace V} :
-- imply
  spinProd A (flipV s) = (-1) ^ A.card * spinProd A s := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.spinProd_flipV G A s

/--
[spinProd_flipV_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma spinProd_flipV_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {s : ConfigSpace V}
-- given
  (hA : Even A.card) :
-- imply
  spinProd A (flipV s) = spinProd A s := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.spinProd_flipV_even G A hA s

/--
[spinProd_flipV_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma spinProd_flipV_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {s : ConfigSpace V}
-- given
  (hA : Odd A.card) :
-- imply
  spinProd A (flipV s) = -spinProd A s := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.spinProd_flipV_odd G A hA s

/--
[fgd_num_neg_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma fgd_num_neg_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hA : Even A.card) :
-- imply
  (∑ s : ConfigSpace V, spinProd A s * isingWeight G β (-h) s) = ∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.fgd_num_neg_even G β h A hA

/--
[fgd_num_neg_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma fgd_num_neg_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hA : Odd A.card) :
-- imply
  (∑ s : ConfigSpace V, spinProd A s * isingWeight G β (-h) s) = -∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.fgd_num_neg_odd G β h A hA

/--
[someEmb_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma someEmb_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V} :
-- imply
  someEmb x = some x := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.someEmb_apply G x

/--
[sum_option_config](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma sum_option_config_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : (Option V → Bool) → ℝ} :
-- imply
  (∑ s : Option V → Bool, f s) = ∑ b : Bool, ∑ τ : V → Bool, f (fun a => Option.rec b τ a) := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.sum_option_config G f

/--
[split_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma split_some_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b : Bool}
  {τ : V → Bool}
  {x : V} :
-- imply
  (fun z => (fun a => Option.rec b τ a : Option V → Bool) (some z)) x = τ x := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.split_some G b τ x

/--
[split_ghost_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma split_ghost_spin_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b : Bool}
  {τ : V → Bool} :
-- imply
  spin (fun a => Option.rec b τ a : Option V → Bool) none = StatMech.Ising.spinB b := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.split_ghost_spin G b τ

/--
[spinProd_map_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma spinProd_map_some_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {b : Bool}
  {τ : V → Bool} :
-- imply
  spinProd (A.map someEmb) (fun a => Option.rec b τ a : Option V → Bool) = spinProd A τ := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.spinProd_map_some G A b τ

/--
[spinProd_insert_none_map_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma spinProd_insert_none_map_some_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {b : Bool}
  {τ : V → Bool} :
-- imply
  spinProd (insert none (A.map someEmb)) (fun a => Option.rec b τ a : Option V → Bool) = StatMech.Ising.spinB b * spinProd A τ := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.spinProd_insert_none_map_some G A b τ

/--
[fgd_partitionJ_ghost_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma fgd_partitionJ_ghost_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  partitionJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) = 2 * isingZ G β h := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.fgd_partitionJ_ghost_eq G β h

/--
[fgd_num_ghost_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma fgd_num_ghost_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hA : Even A.card) :
-- imply
  (∑ s : ConfigSpace (Option V), spinProd (A.map someEmb) s * boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) s) = 2 * ∑ τ : ConfigSpace V, spinProd A τ * isingWeight G β h τ := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.fgd_num_ghost_eq G β h A hA

/--
[fgd_num_ghost_eq_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma fgd_num_ghost_eq_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hA : Odd A.card) :
-- imply
  (∑ s : ConfigSpace (Option V), spinProd (insert none (A.map someEmb)) s * boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) s) = 2 * ∑ τ : ConfigSpace V, spinProd A τ * isingWeight G β h τ := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.fgd_num_ghost_eq_odd G β h A hA

/--
[fgd_expectationJ_ghost_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma fgd_expectationJ_ghost_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hA : Even A.card) :
-- imply
  expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (A.map someEmb) = isingExpectation G β h (spinProd A) := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.fgd_expectationJ_ghost_eq G β h A hA

/--
[fgd_expectationJ_ghost_eq_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma fgd_expectationJ_ghost_eq_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hA : Odd A.card) :
-- imply
  expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert none (A.map someEmb)) = isingExpectation G β h (spinProd A) := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.fgd_expectationJ_ghost_eq_odd G β h A hA

/--
[fgd_isingExpectation_eq_currentSum_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma fgd_isingExpectation_eq_currentSum_ratio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hA : Even A.card) :
-- imply
  isingExpectation G β h (spinProd A) = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (A.map someEmb) / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.fgd_isingExpectation_eq_currentSum_ratio G β h A hA

/--
[fgd_isingExpectation_eq_currentSum_ratio_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma fgd_isingExpectation_eq_currentSum_ratio_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hA : Odd A.card) :
-- imply
  isingExpectation G β h (spinProd A) = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert none (A.map someEmb)) / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.fgd_isingExpectation_eq_currentSum_ratio_odd G β h A hA

/--
[fgd_expectationJ_ghost_eq_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma fgd_expectationJ_ghost_eq_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  expectationJ (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) (({0, 1} : Finset (Fin 3)).map someEmb) = isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1} : Finset (Fin 3))) := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.fgd_expectationJ_ghost_eq_nonvacuous G

/--
[fgd_isingExpectation_eq_currentSum_ratio_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma fgd_isingExpectation_eq_currentSum_ratio_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1} : Finset (Fin 3))) = currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) (({0, 1} : Finset (Fin 3)).map someEmb) / currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.fgd_isingExpectation_eq_currentSum_ratio_nonvacuous G

/--
[map_symmDiff'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma map_symmDiff'_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq W]
  {A B : Finset V}
  {f : V ↪ W} :
-- imply
  (A ∆ B).map f = (A.map f) ∆ (B.map f) := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.map_symmDiff' G A B f

/--
[fgd_ghostCurrentRep_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean)
-/
@[path]
private lemma fgd_ghostCurrentRep_unconditional_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {u v : V}
-- given
  (β h : ℝ)
  (huv : u ≠ v)
  (hA : Even A.card)
  (hAuv : Even ((A ∆ {u, v}).card))
  (huvcard : Even (({u, v} : Finset V).card))
  (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
-- imply
  (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2 * (isingExpectation G β h (spinProd A) - isingExpectation G β h (spinProd (A ∆ {u, v})) * isingExpectation G β h (spinProd {u, v})) = sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (A.map someEmb) ∅ (some u) (some v) := by
-- proof
  apply StatMech.Sharpness.FieldGhostDict.fgd_ghostCurrentRep_unconditional G β h A huv hA hAuv huvcard hZne


-- created on 2026-10-23
