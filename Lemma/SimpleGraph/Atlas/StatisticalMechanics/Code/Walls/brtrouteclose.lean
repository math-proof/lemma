import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.brtrouteclose
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[brt_reachable_of_avoidWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brtrouteclose.lean)
-/
@[path]
private lemma brt_reachable_of_avoidWalk_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {z : Site d}
  {u v : Site d}
  {p : (openSubgraph d ω).Walk u v}
-- given
  (hp : ∀ w ∈ p.support, w ∉ bc61_boxAround d L z) :
-- imply
  (bc67_contractedLattice ω L z).Reachable u v := by
-- proof
  apply StatMech.Walls.brt_reachable_of_avoidWalk ω L z p hp

/--
[brt_adj_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brtrouteclose.lean)
-/
@[path]
private lemma brt_adj_transfer_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {x z a b : Site d}
-- given
  (h : (bc67_contractedLattice ω L x).Adj a b)
  (ha : a ∉ bc61_boxAround d L z)
  (hb : b ∉ bc61_boxAround d L z) :
-- imply
  (bc67_contractedLattice ω L z).Adj a b := by
-- proof
  apply StatMech.Walls.brt_adj_transfer ω L x z a b h ha hb

/--
[brt_ray_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brtrouteclose.lean)
-/
@[path]
private lemma brt_ray_reach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {x z : Site d}
  {r : ℕ → Site d}
-- given
  (hadj : ∀ k, (bc67_contractedLattice ω L x).Adj (r k) (r (k + 1)))
  (havoid : ∀ k, r k ∉ bc61_boxAround d L z) :
-- imply
  ∀ k, (bc67_contractedLattice ω L z).Reachable (r 0) (r k) := by
-- proof
  apply StatMech.Walls.brt_ray_reach ω L x z r hadj havoid

/--
[brt_boxAvoiding_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brtrouteclose.lean)
-/
@[path]
private lemma brt_boxAvoiding_reach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {x z arm : Site d}
-- given
  (hinf : (cluster d (removeSites (bc61_boxAround d L x) ω) arm).Infinite) :
-- imply
  ∃ b : Site d, (bc67_contractedLattice ω L x).Reachable arm b ∧ ∃ r : ℕ → Site d, r 0 = b ∧ Function.Injective r ∧ (∀ k, r k ∉ bc61_boxAround d L z) ∧ (∀ k, (bc67_contractedLattice ω L z).Reachable b (r k)) := by
-- proof
  apply StatMech.Walls.brt_boxAvoiding_reach ω L x z arm hinf

/--
[brt_hroute_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brtrouteclose.lean)
-/
@[path]
private lemma brt_hroute_step_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {aj x b ai : Site d}
-- given
  (hxb : (bc67_contractedLattice ω L aj).Reachable x b)
  (hbai : (bc67_contractedLattice ω L aj).Reachable b ai) :
-- imply
  (bc67_contractedLattice ω L aj).Reachable x ai := by
-- proof
  apply StatMech.Walls.brt_hroute_step ω L aj x b ai hxb hbai

/--
[brt_origin_no_openEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brtrouteclose.lean)
-/
@[path]
private lemma brt_origin_no_openEdge_eq
  {d : ℕ}
  {v : Site 2} :
-- imply
  bc60_upperLines s((0 : Site 2), v) ≠ true := by
-- proof
  apply StatMech.Walls.brt_origin_no_openEdge v

/--
[brt_contractedLattice_no_adj_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brtrouteclose.lean)
-/
@[path]
private lemma brt_contractedLattice_no_adj_origin_eq
  {d : ℕ}
  {L : ℕ}
  {z v : Site 2} :
-- imply
  ¬ (bc67_contractedLattice bc60_upperLines L z).Adj 0 v := by
-- proof
  apply StatMech.Walls.brt_contractedLattice_no_adj_origin L z v

/--
[brt_origin_reach_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brtrouteclose.lean)
-/
@[path]
private lemma brt_origin_reach_eq_eq
  {d : ℕ}
  {L : ℕ}
  {z w : Site 2}
-- given
  (h : (bc67_contractedLattice bc60_upperLines L z).Reachable 0 w) :
-- imply
  w = 0 := by
-- proof
  apply StatMech.Walls.brt_origin_reach_eq L z w h

/--
[brt_hroute_false_on_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brtrouteclose.lean)
-/
@[path]
private lemma brt_hroute_false_on_witness_eq
  {d : ℕ}
  {L : ℕ}
  {a : Fin 3 → Site 2}
-- given
  (hane : ∀ i, a i ≠ 0) :
-- imply
  ¬ (∀ i j, i ≠ j → (bc67_contractedLattice bc60_upperLines L (a j)).Reachable (0 : Site 2) (a i)) := by
-- proof
  apply StatMech.Walls.brt_hroute_false_on_witness L a hane

/--
[brt_witness_trif_but_no_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brtrouteclose.lean)
-/
@[path]
private lemma brt_witness_trif_but_no_route_eq
  {d : ℕ}
  {L : ℕ}
  {a : Fin 3 → Site 2}
-- given
  (hL : 3 ≤ L)
  (hane : ∀ i, a i ≠ 0) :
-- imply
  bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧ ¬ (∀ i j, i ≠ j → (bc67_contractedLattice bc60_upperLines L (a j)).Reachable (0 : Site 2) (a i)) := by
-- proof
  apply StatMech.Walls.brt_witness_trif_but_no_route hL a hane

/--
[brt_witness_tail_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brtrouteclose.lean)
-/
@[path]
private lemma brt_witness_tail_fires_eq
  {d : ℕ}
  {L : ℕ}
  {z : Site 2}
-- given
  (hL : 3 ≤ L) :
-- imply
  ∃ arm b : Site 2, (bc67_contractedLattice bc60_upperLines L 0).Reachable arm b ∧ ∃ r : ℕ → Site 2, r 0 = b ∧ Function.Injective r ∧ (∀ k, r k ∉ bc61_boxAround 2 L z) ∧ (∀ k, (bc67_contractedLattice bc60_upperLines L z).Reachable b (r k)) := by
-- proof
  apply StatMech.Walls.brt_witness_tail_fires hL z

/--
[brt_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brtrouteclose.lean)
-/
@[path]
private lemma brt_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x z arm : Site d), (cluster d (removeSites (bc61_boxAround d L x) ω) arm).Infinite → ∃ b : Site d, (bc67_contractedLattice ω L x).Reachable arm b ∧ ∃ r : ℕ → Site d, r 0 = b ∧ Function.Injective r ∧ (∀ k, r k ∉ bc61_boxAround d L z) ∧ (∀ k, (bc67_contractedLattice ω L z).Reachable b (r k))) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (aj x b ai : Site d), (bc67_contractedLattice ω L aj).Reachable x b → (bc67_contractedLattice ω L aj).Reachable b ai → (bc67_contractedLattice ω L aj).Reachable x ai) ∧ (∀ (L : ℕ), 3 ≤ L → ∀ (a : Fin 3 → Site 2), (∀ i, a i ≠ 0) → bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧ ¬ (∀ i j, i ≠ j → (bc67_contractedLattice bc60_upperLines L (a j)).Reachable (0 : Site 2) (a i))) := by
-- proof
  apply StatMech.Walls.brt_status


-- created on 2026-10-23
