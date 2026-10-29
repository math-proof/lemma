import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc51armforest.Part5
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls StatMech.Walls.Bc51Witness


/--
[bc51_subgraph_isAcyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_subgraph_isAcyclic_eq
  {d : ℕ}
  {T T' : SimpleGraph V}
-- given
  (hsub : T ≤ T')
  (h : T'.IsAcyclic) :
-- imply
  T.IsAcyclic := by
-- proof
  apply StatMech.Walls.bc51_subgraph_isAcyclic hsub h

/--
[bc51_arms_vertexDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_arms_vertexDisjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : SimpleGraph (Site d)}
  {x c0 c1 z0 z1 : Site d}
  {w0 : T.Walk c0 z0}
  {w1 : T.Walk c1 z1}
-- given
  (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
  (hw0x : x ∉ w0.support)
  (hw1x : x ∉ w1.support)
  (hcut : ¬ Connected d (removeSite x ω) c0 c1) :
-- imply
  ∀ v, v ∈ w0.support → v ∈ w1.support → False := by
-- proof
  apply StatMech.Walls.bc51_arms_vertexDisjoint ω T hπ w0 hw0x w1 hw1x hcut

/--
[bc51_arms_edgeDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_arms_edgeDisjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : SimpleGraph (Site d)}
  {x c0 c1 z0 z1 : Site d}
  {w0 : T.Walk c0 z0}
  {w1 : T.Walk c1 z1}
-- given
  (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
  (hw0x : x ∉ w0.support)
  (hw1x : x ∉ w1.support)
  (hcut : ¬ Connected d (removeSite x ω) c0 c1) :
-- imply
  ∀ e, e ∈ w0.edges → e ∈ w1.edges → False := by
-- proof
  apply StatMech.Walls.bc51_arms_edgeDisjoint ω T hπ w0 hw0x w1 hw1x hcut

/--
[bc51_survivor_of_trif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_survivor_of_trif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : SimpleGraph (Site d)}
  {B : Set (Site d)}
  {x : Site d}
  {c zr : Fin 3 → Site d}
-- given
  (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
  (hadj : ∀ i, T.Adj x (c i))
  (hcut01 : ¬ Connected d (removeSite x ω) (c 0) (c 1))
  (hreach : ∀ i, zr i ∈ B ∧ ∃ w : T.Walk (c i) (zr i), x ∉ w.support) :
-- imply
  spc_OnBPath T B x := by
-- proof
  apply StatMech.Walls.bc51_survivor_of_trif ω T hπ B hadj hcut01 hreach

/--
[bc51_armForestReaching_of_globalArmForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_armForestReaching_of_globalArmForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc51_GlobalArmForest ω n) :
-- imply
  sfa_ArmForestReaching ω n := by
-- proof
  apply StatMech.Walls.bc51_armForestReaching_of_globalArmForest ω n h

/--
[bc51_Tcount_le_boundary_of_globalArmForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_Tcount_le_boundary_of_globalArmForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc51_GlobalArmForest ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc51_Tcount_le_boundary_of_globalArmForest ω n h

/--
[bc51_armForestEmbedding_iff_globalArmForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_armForestEmbedding_iff_globalArmForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc51_ArmForestEmbedding ω n ↔ bc51_GlobalArmForest ω n := by
-- proof
  apply StatMech.Walls.bc51_armForestEmbedding_iff_globalArmForest ω n

/--
[bc51_armForestReaching_of_armEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_armForestReaching_of_armEmbedding_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc51_ArmForestEmbedding ω n) :
-- imply
  sfa_ArmForestReaching ω n := by
-- proof
  apply StatMech.Walls.bc51_armForestReaching_of_armEmbedding ω n h

/--
[bc51_openSubgraph_removeSite_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_openSubgraph_removeSite_le_eq
  {d : ℕ}
  {x : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  openSubgraph d (removeSite x ω) ≤ openSubgraph d ω := by
-- proof
  apply StatMech.Walls.bc51_openSubgraph_removeSite_le x ω

/--
[bc51_cutWalk_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_cutWalk_lift_eq
  {d : ℕ}
  {x a b : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {w : (openSubgraph d (removeSite x ω)).Walk a b}
-- given
  (hwx : x ∉ w.support) :
-- imply
  ∃ w' : (openSubgraph d ω).Walk a b, x ∉ w'.support ∧ (∀ e, e ∈ w'.edges → e ∈ (openSubgraph d ω).edgeSet) := by
-- proof
  apply StatMech.Walls.bc51_cutWalk_lift w hwx

/--
[bc51_walk_transfer_to_T](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_walk_transfer_to_T_eq
  {d : ℕ}
  {a b x : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : SimpleGraph (Site d)}
  {w' : (openSubgraph d ω).Walk a b}
-- given
  (hwx : x ∉ w'.support)
  (hcov : ∀ e, e ∈ w'.edges → e ∈ T.edgeSet) :
-- imply
  ∃ w : T.Walk a b, x ∉ w.support := by
-- proof
  apply StatMech.Walls.bc51_walk_transfer_to_T T w' hwx hcov

/--
[bc51_globalArmForest_of_forestCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_globalArmForest_of_forestCover_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {Vall : Finset (Site d)}
  {T : SimpleGraph (Site d)}
  {B : Set (Site d)}
  {c : Site d → Fin 3 → Site d}
  {zr : Site d → Fin 3 → Site d}
-- given
  (hTdec : DecidableRel T.Adj)
  (hTac : T.IsAcyclic)
  (hTopen : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
  (hTsupp : ∀ u v, T.Adj u v → u ∈ Vall)
  (hBbd : B ⊆ vertexBoundary d n)
  (hsurv : (∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) ∨ (∃ v, spc_OnBPath T B v))
  (hData : ∀ x, x ∈ box d n → IsTrifurcation d ω x → (∀ i, T.Adj x (c x i)) ∧ (¬ Connected d (removeSite x ω) (c x 0) (c x 1) ∧ ¬ Connected d (removeSite x ω) (c x 0) (c x 2) ∧ ¬ Connected d (removeSite x ω) (c x 1) (c x 2)) ∧ (∀ i, zr x i ∈ B ∧ ∃ w : (openSubgraph d (removeSite x ω)).Walk (c x i) (zr x i), x ∉ w.support ∧ (∀ e, e ∈ (w.mapLe (bc51_openSubgraph_removeSite_le x ω)).edges → e ∈ T.edgeSet))) :
-- imply
  bc51_GlobalArmForest ω n := by
-- proof
  apply StatMech.Walls.bc51_globalArmForest_of_forestCover ω n Vall T hTdec B c zr hTac hTopen hTsupp hBbd hsurv hData

/--
[bc51_arc_perArm_reaching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_arc_perArm_reaching_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
-- given
  (hres : arc_TrifArmsRemoveSiteInfinite ω n)
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x) :
-- imply
  ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d), (∀ i, (openSubgraph d ω).Adj x (c i)) ∧ (∀ i, c i ≠ x) ∧ (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧ ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧ ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧ (∀ i, zr i ∈ vertexBoundary d (n + 1) ∧ ∃ w : (openSubgraph d (removeSite x ω)).Walk (c i) (zr i), x ∉ w.support) := by
-- proof
  apply StatMech.Walls.bc51_arc_perArm_reaching ω n hres x hxbox htri

/--
[bc51_globalArmForest_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_globalArmForest_star_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
  {a : Fin 3 → Site d}
-- given
  (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x)
  (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
  (habdry : ∀ i, a i ∈ vertexBoundary d n)
  (hxne : ∀ i, a i ≠ x)
  (hainj : Function.Injective a)
  (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧ ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧ ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
-- imply
  bc51_GlobalArmForest ω n := by
-- proof
  apply StatMech.Walls.bc51_globalArmForest_star ω n a hsingle hxbox htri hadj habdry hxne hainj hsep

/--
[bc51_globalArmForest_of_boundary_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_globalArmForest_of_boundary_edge_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {b₁ b₂ : Site d}
-- given
  (hb1 : b₁ ∈ vertexBoundary d n)
  (hb2 : b₂ ∈ vertexBoundary d n)
  (hbne : b₁ ≠ b₂)
  (hopen : (openSubgraph d ω).Adj b₁ b₂)
  (hnotrif : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc51_GlobalArmForest ω n := by
-- proof
  apply StatMech.Walls.bc51_globalArmForest_of_boundary_edge ω n hb1 hb2 hbne hopen hnotrif

/--
[catG_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma catG_isTree_eq
  {d : ℕ} :
-- imply
  catG.IsTree := by
-- proof
  apply StatMech.Walls.Bc51Witness.catG_isTree

/--
[catG_leafCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma catG_leafCount_eq
  {d : ℕ} :
-- imply
  (univ.filter (fun v => 3 ≤ catG.degree v)).card = 2 ∧ (univ.filter (fun v => catG.degree v = 1)).card = 4 := by
-- proof
  apply StatMech.Walls.Bc51Witness.catG_leafCount

/--
[catG_internal_lt_leaves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma catG_internal_lt_leaves_eq
  {d : ℕ} :
-- imply
  (univ.filter (fun v => 3 ≤ catG.degree v)).card < (univ.filter (fun v => catG.degree v = 1)).card := by
-- proof
  apply StatMech.Walls.Bc51Witness.catG_internal_lt_leaves

/--
[cycleG_not_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma cycleG_not_acyclic_eq
  {d : ℕ} :
-- imply
  ¬ cycleG.IsAcyclic := by
-- proof
  apply StatMech.Walls.Bc51Witness.cycleG_not_acyclic

/--
[catG_subgraph_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma catG_subgraph_acyclic_eq
  {d : ℕ}
  {H : SimpleGraph (Fin 6)}
-- given
  (hsub : H ≤ catG) :
-- imply
  H.IsAcyclic := by
-- proof
  apply StatMech.Walls.Bc51Witness.catG_subgraph_acyclic hsub

/--
[bc51_forestCover_nonvacuous_nilWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_forestCover_nonvacuous_nilWalk_eq
  {d : ℕ}
  {x a : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : SimpleGraph (Site d)}
-- given
  (hax : a ≠ x) :
-- imply
  let w : (openSubgraph d (removeSite x ω)).Walk a a := Walk.nil x ∉ w.support ∧ (∀ e, e ∈ (w.mapLe (bc51_openSubgraph_removeSite_le x ω)).edges → e ∈ T.edgeSet) := by
-- proof
  apply StatMech.Walls.bc51_forestCover_nonvacuous_nilWalk T hax

/--
[bc51_globalArmForest_nonvacuous_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_globalArmForest_nonvacuous_star_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
  {a : Fin 3 → Site d}
-- given
  (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x)
  (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
  (habdry : ∀ i, a i ∈ vertexBoundary d n)
  (hxne : ∀ i, a i ≠ x)
  (hainj : Function.Injective a)
  (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧ ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧ ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
-- imply
  bc51_GlobalArmForest ω n := by
-- proof
  apply StatMech.Walls.bc51_globalArmForest_nonvacuous_star ω n a hsingle hxbox htri hadj habdry hxne hainj hsep

/--
[bc51_burton_keane_bernoulli_of_globalArmForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean)
-/
@[path]
private lemma bc51_burton_keane_bernoulli_of_globalArmForest_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (harm : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc51_GlobalArmForest ω n)
  (hroute : ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc51_burton_keane_bernoulli_of_globalArmForest hd p hp1 hp0 harm hroute


-- created on 2026-10-23
