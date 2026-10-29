import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.benentryleg.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[ben_ray34_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_ray34_gap_eq
  {d : ℕ}
  [DecidableEq V]
  {G : SimpleGraph V}
  [LocallyFinite G]
  {v : V}
  {T : Finset V}
-- given
  (hinf : (ray34_AvoidCluster G ∅ v).Infinite) :
-- imply
  ∃ b, ray34_AvoidReach G ∅ v b ∧ (ray34_AvoidCluster G (↑T) b).Infinite := by
-- proof
  apply StatMech.Walls.ben_ray34_gap hinf T

/--
[ben_box_adj_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_box_adj_avoids_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {t a b : Site d}
-- given
  (h : (bc67_contractedLattice ω L t).Adj a b) :
-- imply
  a ∉ bc61_boxAround d L t ∧ b ∉ bc61_boxAround d L t := by
-- proof
  apply StatMech.Walls.ben_box_adj_avoids ω L t a b h

/--
[ben_escape_of_notEnclosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_escape_of_notEnclosed_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {tipj x : Site d}
-- given
  (hxinf : (cluster d (removeSites (bc61_boxAround d L tipj) ω) x).Infinite) :
-- imply
  ∃ r : ℕ → Site d, r 0 = x ∧ Function.Injective r ∧ (∀ k, (bc67_contractedLattice ω L tipj).Adj (r k) (r (k + 1))) ∧ (∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1))) ∧ (∀ k, r k ∉ bc61_boxAround d L tipj) := by
-- proof
  apply StatMech.Walls.ben_escape_of_notEnclosed ω L tipj x hxinf

/--
[ben_ray_reach_in_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_ray_reach_in_compl_eq
  {d : ℕ}
  {Bset : Set (Site d)}
  {r : ℕ → Site d}
  {k : ℕ}
-- given
  (hlat : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)))
  (havoid : ∀ k, r k ∉ Bset) :
-- imply
  ((hypercubicLattice d).induce Bsetᶜ).Reachable ⟨r 0, havoid 0⟩ ⟨r k, havoid k⟩ := by
-- proof
  apply StatMech.Walls.ben_ray_reach_in_compl Bset r hlat havoid k

/--
[ben_ray_reaches_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_ray_reaches_exterior_eq
  {d : ℕ}
  {Bset : Set (Site d)}
  {R : ℕ}
  {r : ℕ → Site d}
-- given
  (hBR : Bset ⊆ box d R)
  (hinj : Function.Injective r)
  (hlat : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)))
  (havoid : ∀ k, r k ∉ Bset) :
-- imply
  ∃ k, r k ∈ exterior d R ∧ ((hypercubicLattice d).induce Bsetᶜ).Reachable ⟨r 0, havoid 0⟩ ⟨r k, havoid k⟩ := by
-- proof
  apply StatMech.Walls.ben_ray_reaches_exterior Bset R hBR r hinj hlat havoid

/--
[ben_escapes_same_fullComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_escapes_same_fullComponent_eq
  {d : ℕ}
  {F : Finset (Site d)}
  {r s : ℕ → Site d}
-- given
  (hd : 2 ≤ d)
  (hrinj : Function.Injective r)
  (hsinj : Function.Injective s)
  (hrlat : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)))
  (hslat : ∀ k, (hypercubicLattice d).Adj (s k) (s (k + 1)))
  (hravoid : ∀ k, r k ∉ (↑F : Set (Site d)))
  (hsavoid : ∀ k, s k ∉ (↑F : Set (Site d))) :
-- imply
  ((hypercubicLattice d).induce (↑F : Set (Site d))ᶜ).Reachable ⟨r 0, hravoid 0⟩ ⟨s 0, hsavoid 0⟩ := by
-- proof
  apply StatMech.Walls.ben_escapes_same_fullComponent F hd r s hrinj hsinj hrlat hslat hravoid hsavoid

/--
[ben_entry_of_clusterReconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_entry_of_clusterReconnect_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {tipj x b : Site d}
-- given
  (hxb : (openSubgraph d ω).Reachable x b)
  (hxesc : (cluster d (removeSites (bc61_boxAround d L tipj) ω) x).Infinite)
  (hbesc : (cluster d (removeSites (bc61_boxAround d L tipj) ω) b).Infinite)
  (hrec : ben_ClusterReconnect ω L tipj) :
-- imply
  (bc67_contractedLattice ω L tipj).Reachable x b := by
-- proof
  apply StatMech.Walls.ben_entry_of_clusterReconnect ω L tipj x b hxb hxesc hbesc hrec

/--
[ben_full_reconnect_of_escapes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_full_reconnect_of_escapes_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {tipj x b : Site d}
-- given
  (hd : 2 ≤ d)
  (hxesc : (cluster d (removeSites (bc61_boxAround d L tipj) ω) x).Infinite)
  (hbesc : (cluster d (removeSites (bc61_boxAround d L tipj) ω) b).Infinite) :
-- imply
  ∃ (hx : x ∉ (↑(bc61_boxAround d L tipj) : Set (Site d))) (hb : b ∉ (↑(bc61_boxAround d L tipj) : Set (Site d))), ((hypercubicLattice d).induce (↑(bc61_boxAround d L tipj) : Set (Site d))ᶜ).Reachable ⟨x, hx⟩ ⟨b, hb⟩ := by
-- proof
  apply StatMech.Walls.ben_full_reconnect_of_escapes ω L hd tipj x b hxesc hbesc

/--
[ben_entry_clause_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_entry_clause_of_residue_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {x : Site d}
  {tip b : Fin 3 → Site d}
-- given
  (hrec : ∀ j, ben_ClusterReconnect ω L (tip j))
  (hxb : ∀ i, (openSubgraph d ω).Reachable x (b i))
  (hxesc : ∀ i j, i ≠ j → (cluster d (removeSites (bc61_boxAround d L (tip j)) ω) x).Infinite)
  (hbesc : ∀ i j, i ≠ j → (cluster d (removeSites (bc61_boxAround d L (tip j)) ω) (b i)).Infinite) :
-- imply
  ∀ i j, i ≠ j → (bc67_contractedLattice ω L (tip j)).Reachable x (b i) := by
-- proof
  apply StatMech.Walls.ben_entry_clause_of_residue ω L x tip b hrec hxb hxesc hbesc

/--
[ben_repRoute_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_repRoute_of_residue_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {x : Site d}
  {tip b : Fin 3 → Site d}
-- given
  (hrec : ∀ j, ben_ClusterReconnect ω L (tip j))
  (hxb : ∀ i, (openSubgraph d ω).Reachable x (b i))
  (hxesc : ∀ i j, i ≠ j → (cluster d (removeSites (bc61_boxAround d L (tip j)) ω) x).Infinite)
  (hbesc : ∀ i j, i ≠ j → (cluster d (removeSites (bc61_boxAround d L (tip j)) ω) (b i)).Infinite)
  (htail : ∀ i j, i ≠ j → (bc67_contractedLattice ω L (tip j)).Reachable (b i) (tip i)) :
-- imply
  bcr_RepRoute ω L x tip := by
-- proof
  apply StatMech.Walls.ben_repRoute_of_residue ω L x tip b hrec hxb hxesc hbesc htail

/--
[ben_bk_of_trifData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_bk_of_trifData_eq
  {d : ℕ}
-- given
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bgc_TrifForestData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.ben_bk_of_trifData p hp1 hp0 hdata

/--
[ben_residue_is_openLift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_residue_is_openLift_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {tipj : Site d}
-- given
  (hd : 2 ≤ d) :
-- imply
  ben_ClusterReconnect ω L tipj ↔ (∀ u v : Site d, (openSubgraph d ω).Reachable u v → (cluster d (removeSites (bc61_boxAround d L tipj) ω) u).Infinite → (cluster d (removeSites (bc61_boxAround d L tipj) ω) v).Infinite → (∃ (hu : u ∉ (↑(bc61_boxAround d L tipj) : Set (Site d))) (hv : v ∉ (↑(bc61_boxAround d L tipj) : Set (Site d))), ((hypercubicLattice d).induce (↑(bc61_boxAround d L tipj) : Set (Site d))ᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩) → (bc67_contractedLattice ω L tipj).Reachable u v) := by
-- proof
  apply StatMech.Walls.ben_residue_is_openLift ω L hd tipj

/--
[ben_axis_out_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_axis_out_x_eq
  {d : ℕ}
  {L : ℕ}
  {c : ℤ}
-- given
  (h : L < c.natAbs) :
-- imply
  bc57_pt c 0 ∉ (↑(bc61_boxAround 2 L (bc57_pt 0 0)) : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.ben_axis_out_x L c h

/--
[ben_axis_out_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_axis_out_y_eq
  {d : ℕ}
  {L : ℕ}
  {c : ℤ}
-- given
  (h : L < c.natAbs) :
-- imply
  bc57_pt 0 c ∉ (↑(bc61_boxAround 2 L (bc57_pt 0 0)) : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.ben_axis_out_y L c h

/--
[ben_natAbs_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_natAbs_far_eq
  {d : ℕ}
  {L k : ℕ} :
-- imply
  L < ((L : ℤ) + 1 + (k : ℤ)).natAbs := by
-- proof
  apply StatMech.Walls.ben_natAbs_far L k

/--
[ben_freeReconnect_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_freeReconnect_witness_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  ((hypercubicLattice 2).induce (↑(bc61_boxAround 2 L (bc57_pt 0 0)) : Set (Site 2))ᶜ).Reachable ⟨bc57_pt ((L : ℤ) + 1) 0, ben_axis_out_x L ((L : ℤ) + 1) (by rw [show ((L : ℤ) + 1) = ((L + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]; omega)⟩ ⟨bc57_pt 0 ((L : ℤ) + 1), ben_axis_out_y L ((L : ℤ) + 1) (by rw [show ((L : ℤ) + 1) = ((L + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]; omega)⟩ := by
-- proof
  apply StatMech.Walls.ben_freeReconnect_witness L

/--
[ben_entry_conclusion_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_entry_conclusion_satisfiable_eq
  {d : ℕ}
  {L R : ℕ}
-- given
  (hR : L < R) :
-- imply
  bcr_RepRoute bcr_cross L (bc57_pt 0 0) (brp_witArm R) := by
-- proof
  apply StatMech.Walls.ben_entry_conclusion_satisfiable L R hR

/--
[ben_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean)
-/
@[path]
private lemma ben_status_eq
  {d : ℕ} :
-- imply
  (∀ {V : Type} [inst : DecidableEq V] {G : SimpleGraph V} [inst2 : LocallyFinite G] {v : V}, (ray34_AvoidCluster G ∅ v).Infinite → ∀ (T : Finset V), ∃ b, ray34_AvoidReach G ∅ v b ∧ (ray34_AvoidCluster G (↑T) b).Infinite) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ), 2 ≤ d → ∀ (tipj x b : Site d), (cluster d (removeSites (bc61_boxAround d L tipj) ω) x).Infinite → (cluster d (removeSites (bc61_boxAround d L tipj) ω) b).Infinite → ∃ (hx : x ∉ (↑(bc61_boxAround d L tipj) : Set (Site d))) (hb : b ∉ (↑(bc61_boxAround d L tipj) : Set (Site d))), ((hypercubicLattice d).induce (↑(bc61_boxAround d L tipj) : Set (Site d))ᶜ).Reachable ⟨x, hx⟩ ⟨b, hb⟩) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (tipj x b : Site d), (openSubgraph d ω).Reachable x b → (cluster d (removeSites (bc61_boxAround d L tipj) ω) x).Infinite → (cluster d (removeSites (bc61_boxAround d L tipj) ω) b).Infinite → ben_ClusterReconnect ω L tipj → (bc67_contractedLattice ω L tipj).Reachable x b) := by
-- proof
  apply StatMech.Walls.ben_status


-- created on 2026-10-23
