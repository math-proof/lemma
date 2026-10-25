import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc122carrier.Part5
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc122_carrier_closes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_carrier_closes_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc122_StarOfArms ω L R) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bc122_carrier_closes ω L R h

/--
[bc122_count_via_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_count_via_carrier_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc122_StarOfArms ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc122_count_via_carrier ω L R h

/--
[bc122_mem_hubs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_mem_hubs_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y : Site d} :
-- imply
  y ∈ bc122_hubs ω L R ↔ y ∈ box d R ∧ bc67_IsGnTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.bc122_mem_hubs

/--
[bc122_hub_mem_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_hub_mem_carrier_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
  {y : Site d}
-- given
  (hy : y ∈ bc122_hubs ω L R) :
-- imply
  y ∈ bc122_carrier ω L R arm := by
-- proof
  apply StatMech.Walls.bc122_hub_mem_carrier hy

/--
[bc122_tip_mem_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_tip_mem_carrier_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
  {y : Site d}
  {j : Fin 3}
-- given
  (hy : y ∈ bc122_hubs ω L R) :
-- imply
  arm y j ∈ bc122_carrier ω L R arm := by
-- proof
  apply StatMech.Walls.bc122_tip_mem_carrier hy j

/--
[bc122_starRel_tip_forces_hub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_starRel_tip_forces_hub_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
  {y : Site d}
  {j : Fin 3}
  {w : Site d}
-- given
  (hHBA : bc122_HubBoundaryArms ω L R arm)
  (hy : y ∈ bc122_hubs ω L R)
  (h : bc122_starRel ω L R arm (arm y j) w ∨ bc122_starRel ω L R arm w (arm y j)) :
-- imply
  w = y := by
-- proof
  apply StatMech.Walls.bc122_starRel_tip_forces_hub hHBA hy h

/--
[bc122_starGraph_tip_adj_forces_hub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_starGraph_tip_adj_forces_hub_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
  {y : Site d}
  {j : Fin 3}
  {lv w' : ↑(bc122_carrier ω L R arm)}
-- given
  (hHBA : bc122_HubBoundaryArms ω L R arm)
  (hy : y ∈ bc122_hubs ω L R)
  (hlv : (lv : Site d) = arm y j)
  (hadj : (bc122_starGraph ω L R arm).Adj lv w') :
-- imply
  (w' : Site d) = y := by
-- proof
  apply StatMech.Walls.bc122_starGraph_tip_adj_forces_hub hHBA hy hlv hadj

/--
[bc122_tip_isolated_in_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_tip_isolated_in_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
  {y : Site d}
  {j : Fin 3}
  {w' : ↑(bc122_carrier ω L R arm)}
-- given
  (hHBA : bc122_HubBoundaryArms ω L R arm)
  (hy : y ∈ bc122_hubs ω L R)
  (hub lv : ↑(bc122_carrier ω L R arm))
  (hhub : (hub : Site d) = y)
  (hlv : (lv : Site d) = arm y j) :
-- imply
  ¬ ((bc122_starGraph ω L R arm).deleteIncidenceSet hub).Adj lv w' := by
-- proof
  apply StatMech.Walls.bc122_tip_isolated_in_cut hHBA hy hub lv hhub hlv w'

/--
[bc122_tips_not_reachable_in_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_tips_not_reachable_in_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
  {y : Site d}
  {j k : Fin 3}
-- given
  (hHBA : bc122_HubBoundaryArms ω L R arm)
  (hy : y ∈ bc122_hubs ω L R)
  (hub lv₁ lv₂ : ↑(bc122_carrier ω L R arm))
  (hhub : (hub : Site d) = y)
  (hlv₁ : (lv₁ : Site d) = arm y j)
  (hlv₂ : (lv₂ : Site d) = arm y k)
  (hne : lv₁ ≠ lv₂) :
-- imply
  ¬ ((bc122_starGraph ω L R arm).deleteIncidenceSet hub).Reachable lv₁ lv₂ := by
-- proof
  apply StatMech.Walls.bc122_tips_not_reachable_in_cut hHBA hy hub lv₁ lv₂ hhub hlv₁ hlv₂ hne

/--
[bc122_starGraph_hub_adj_tip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_starGraph_hub_adj_tip_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
  {y : Site d}
  {j : Fin 3}
-- given
  (hy : y ∈ bc122_hubs ω L R)
  (hub lv : ↑(bc122_carrier ω L R arm))
  (hhub : (hub : Site d) = y)
  (hlv : (lv : Site d) = arm y j)
  (hne : hub ≠ lv) :
-- imply
  (bc122_starGraph ω L R arm).Adj hub lv := by
-- proof
  apply StatMech.Walls.bc122_starGraph_hub_adj_tip hy hub lv hhub hlv hne

/--
[bc122_starGraph_adj_tip_form](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_starGraph_adj_tip_form_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
  {a b : ↑(bc122_carrier ω L R arm)}
-- given
  (hab : (bc122_starGraph ω L R arm).Adj a b) :
-- imply
  (∃ y ∈ bc122_hubs ω L R, ∃ j : Fin 3, (a : Site d) = arm y j ∧ (b : Site d) = y) ∨ (∃ y ∈ bc122_hubs ω L R, ∃ j : Fin 3, (b : Site d) = arm y j ∧ (a : Site d) = y) := by
-- proof
  apply StatMech.Walls.bc122_starGraph_adj_tip_form hab

/--
[bc122_tip_isolated_after_edge_delete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_tip_isolated_after_edge_delete_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
  {y : Site d}
  {j : Fin 3}
  {w' : ↑(bc122_carrier ω L R arm)}
-- given
  (hHBA : bc122_HubBoundaryArms ω L R arm)
  (hy : y ∈ bc122_hubs ω L R)
  (hub lv : ↑(bc122_carrier ω L R arm))
  (hhub : (hub : Site d) = y)
  (hlv : (lv : Site d) = arm y j) :
-- imply
  ¬ ((bc122_starGraph ω L R arm).deleteEdges {s(hub, lv)}).Adj lv w' := by
-- proof
  apply StatMech.Walls.bc122_tip_isolated_after_edge_delete hHBA hy hub lv hhub hlv w'

/--
[bc122_starGraph_edge_isBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_starGraph_edge_isBridge_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
  {a b : ↑(bc122_carrier ω L R arm)}
-- given
  (hHBA : bc122_HubBoundaryArms ω L R arm)
  (hab : (bc122_starGraph ω L R arm).Adj a b) :
-- imply
  (bc122_starGraph ω L R arm).IsBridge s(a, b) := by
-- proof
  apply StatMech.Walls.bc122_starGraph_edge_isBridge hHBA hab

/--
[bc122_starGraph_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_starGraph_acyclic_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
-- given
  (hHBA : bc122_HubBoundaryArms ω L R arm) :
-- imply
  (bc122_starGraph ω L R arm).IsAcyclic := by
-- proof
  apply StatMech.Walls.bc122_starGraph_acyclic hHBA

/--
[bc122_](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122__eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
  {base : ↑(bc122_carrier ω L R arm)}
  {z : Site d}
-- given
  (hz : z ∈ bc122_carrier ω L R arm) :
-- imply
  (bc122_ιU ω L R arm base z : Site d) = z := by
-- proof
  apply StatMech.Walls.bc122_ hz

/--
[bc122_](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122__eq_2
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
  {base : ↑(bc122_carrier ω L R arm)}
  {z : Site d}
-- given
  (hz : z ∈ bc122_hubs ω L R) :
-- imply
  (bc122_ιU ω L R arm base z : Site d) = z := by
-- proof
  apply StatMech.Walls.bc122_ hz

/--
[bc122_boundaryStar_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_boundaryStar_globalForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
  {base : ↑(bc122_carrier ω L R arm)}
-- given
  (hHBA : bc122_HubBoundaryArms ω L R arm)
  (hFmin : ∀ (F : SimpleGraph (↑(bc122_carrier ω L R arm) : Type)) [DecidableRel F.Adj], F ≤ bc122_starGraph ω L R arm → F.IsAcyclic → (∀ v : (↑(bc122_carrier ω L R arm) : Type), F.degree v = 1 → bc121_Protected ω L R (bc122_ιU ω L R arm base) v) → (∀ a b : (↑(bc122_carrier ω L R arm) : Type), bc121_Protected ω L R (bc122_ιU ω L R arm base) a → bc121_Protected ω L R (bc122_ιU ω L R arm base) b → (bc122_starGraph ω L R arm).Reachable a b → F.Reachable a b) → ∀ v : (↑(bc122_carrier ω L R arm) : Type), 1 ≤ F.degree v) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bc122_boundaryStar_globalForest ω L R hHBA base hFmin

/--
[bc122_arm_boundary_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_arm_boundary_reach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y a : Site d}
-- given
  (hR : 1 ≤ R)
  (habox : a ∈ box d R)
  (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
-- imply
  ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z := by
-- proof
  apply StatMech.Walls.bc122_arm_boundary_reach ω L R hR y a habox hinf

/--
[bc122_hubBoundaryArms_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_hubBoundaryArms_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
-- imply
  bc122_HubBoundaryArms ω L R (fun _ _ => (0 : Site d)) := by
-- proof
  apply StatMech.Walls.bc122_hubBoundaryArms_nonvacuous ω L R hno

/--
[bc122_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean)
-/
@[path]
private lemma bc122_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc122_StarOfArms ω L R → bc69_Gn_globalForest ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (arm : Site d → Fin 3 → Site d), bc122_HubBoundaryArms ω L R arm → (bc122_starGraph ω L R arm).IsAcyclic) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R → (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite → ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc122_StarOfArms ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc122_status


-- created on 2026-10-23
