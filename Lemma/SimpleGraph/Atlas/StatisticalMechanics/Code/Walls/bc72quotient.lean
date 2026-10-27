import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc72quotient.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc72_quotGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_quotGraph_adj_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {f : V → B}
  {u v : B} :
-- imply
  (bc72_quotGraph G f).Adj u v ↔ u ≠ v ∧ ∃ a b, f a = u ∧ f b = v ∧ G.Adj a b := by
-- proof
  apply StatMech.Walls.bc72_quotGraph_adj G f u v

/--
[bc72_collapseBox_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_collapseBox_outside_eq
  {d : ℕ}
  {L : ℕ}
  {y x : Site d}
-- given
  (hx : x ∉ bc61_boxAround d L y) :
-- imply
  bc72_collapseBox L y x = x := by
-- proof
  apply StatMech.Walls.bc72_collapseBox_outside hx

/--
[bc72_collapseBox_inside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_collapseBox_inside_eq
  {d : ℕ}
  {L : ℕ}
  {y x : Site d}
-- given
  (hx : x ∈ bc61_boxAround d L y) :
-- imply
  bc72_collapseBox L y x = y := by
-- proof
  apply StatMech.Walls.bc72_collapseBox_inside hx

/--
[bc72_collapseBox_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_collapseBox_center_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site d} :
-- imply
  bc72_collapseBox L y y = y := by
-- proof
  apply StatMech.Walls.bc72_collapseBox_center L y

/--
[bc72_y_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_y_mem_box_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site d} :
-- imply
  y ∈ bc61_boxAround d L y := by
-- proof
  apply StatMech.Walls.bc72_y_mem_box L y

/--
[bc72_collapse_ne_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_collapse_ne_center_eq
  {d : ℕ}
  {L : ℕ}
  {y p : Site d}
-- given
  (h : bc72_collapseBox L y p ≠ y) :
-- imply
  p ∉ bc61_boxAround d L y ∧ bc72_collapseBox L y p = p := by
-- proof
  apply StatMech.Walls.bc72_collapse_ne_center h

/--
[bc72_notMem_of_removeSites_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_notMem_of_removeSites_open_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
-- given
  (h : removeSites T ω s(a, b) = true) :
-- imply
  a ∉ T ∧ b ∉ T := by
-- proof
  apply StatMech.Walls.bc72_notMem_of_removeSites_open h

/--
[bc72_notMem_box_of_cut_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_notMem_box_of_cut_adj_eq
  {d : ℕ}
  {L : ℕ}
  {y a b : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hadj : (openSubgraph d (removeSites (bc61_boxAround d L y) ω)).Adj a b) :
-- imply
  a ∉ bc61_boxAround d L y ∧ b ∉ bc61_boxAround d L y := by
-- proof
  apply StatMech.Walls.bc72_notMem_box_of_cut_adj hadj

/--
[bc72_quot_edge_to_removeSites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_quot_edge_to_removeSites_eq
  {d : ℕ}
  {L : ℕ}
  {y u v : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hadj : (bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).Adj u v)
  (huy : u ≠ y)
  (hvy : v ≠ y) :
-- imply
  (openSubgraph d (removeSites (bc61_boxAround d L y) ω)).Adj u v := by
-- proof
  apply StatMech.Walls.bc72_quot_edge_to_removeSites hadj huy hvy

/--
[bc72_quot_reachable_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_quot_reachable_of_reachable_eq
  {d : ℕ}
  {L : ℕ}
  {y a b : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : Connected d ω a b) :
-- imply
  (bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).Reachable (bc72_collapseBox L y a) (bc72_collapseBox L y b) := by
-- proof
  apply StatMech.Walls.bc72_quot_reachable_of_reachable h

/--
[bc72_removeSites_reachable_of_quot_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_removeSites_reachable_of_quot_avoid_eq
  {d : ℕ}
  {L : ℕ}
  {y u v : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {w : (bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).Walk u v}
-- given
  (hw : y ∉ w.support) :
-- imply
  Connected d (removeSites (bc61_boxAround d L y) ω) u v := by
-- proof
  apply StatMech.Walls.bc72_removeSites_reachable_of_quot_avoid w hw

/--
[bc72_removeSites_of_quotInduce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_removeSites_of_quotInduce_eq
  {d : ℕ}
  {L : ℕ}
  {y a₁ a₂ : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (ha₁ : a₁ ≠ y)
  (ha₂ : a₂ ≠ y)
  (h : ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce ({y}ᶜ : Set (Site d))).Reachable ⟨a₁, by simpa using ha₁⟩ ⟨a₂, by simpa using ha₂⟩) :
-- imply
  Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ := by
-- proof
  apply StatMech.Walls.bc72_removeSites_of_quotInduce ha₁ ha₂ h

/--
[bc72_arm_adjacent_to_superVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_arm_adjacent_to_superVertex_eq
  {d : ℕ}
  {L : ℕ}
  {y a : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hinc : bc67_GnIncident ω L y a)
  (hne : a ∉ bc61_boxAround d L y) :
-- imply
  (bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).Adj y a := by
-- proof
  apply StatMech.Walls.bc72_arm_adjacent_to_superVertex hinc hne

/--
[bc72_arms_nonAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_arms_nonAdjacent_eq
  {d : ℕ}
  {L : ℕ}
  {y a₁ a₂ : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (ha₁ : a₁ ≠ y)
  (ha₂ : a₂ ≠ y)
  (hcut : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂) :
-- imply
  ¬ (bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).Adj a₁ a₂ := by
-- proof
  apply StatMech.Walls.bc72_arms_nonAdjacent ha₁ ha₂ hcut

/--
[bc72_arm_outside_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_arm_outside_of_infinite_eq
  {d : ℕ}
  {L : ℕ}
  {x a : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hinf : (cluster d (removeSites (bc61_boxAround d L x) ω) a).Infinite) :
-- imply
  a ∉ bc61_boxAround d L x := by
-- proof
  apply StatMech.Walls.bc72_arm_outside_of_infinite hinf

/--
[bc72_rs_of_doubleInduce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_rs_of_doubleInduce_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S : Set (Site d)}
  {a₁ a₂ : (↑S : Type)}
-- given
  (hyS : y ∈ S)
  (h0 : a₁ ≠ ⟨y, hyS⟩)
  (h1 : a₂ ≠ ⟨y, hyS⟩)
  (h : (((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).induce ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable ⟨a₁, by simpa using h0⟩ ⟨a₂, by simpa using h1⟩) :
-- imply
  Connected d (removeSites (bc61_boxAround d L y) ω) (a₁ : Site d) (a₂ : Site d) := by
-- proof
  apply StatMech.Walls.bc72_rs_of_doubleInduce hyS h0 h1 h

/--
[bc72_quot_deg3_of_gnTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_quot_deg3_of_gnTrif_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bc67_IsGnTrifurcation ω L y) :
-- imply
  ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : y ∈ S) (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).Adj), 3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).degree ⟨y, hyS⟩ := by
-- proof
  apply StatMech.Walls.bc72_quot_deg3_of_gnTrif h

/--
[bc72_GnForestNeighbours_of_singleHub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_GnForestNeighbours_of_singleHub_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {x : Site d}
  {a : Fin 3 → Site d}
-- given
  (hxbox : x ∈ box d R)
  (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
  (habdry : ∀ i, a i ∈ vertexBoundary d R)
  (hincid : ∀ i, bc67_GnIncident ω L x (a i))
  (haoutside : ∀ i, a i ∉ bc61_boxAround d L x)
  (hcut : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (a i) (a j))
  (hxne : ∀ i, a i ≠ x)
  (hainj : Function.Injective a) :
-- imply
  bc71_GnForestNeighbours ω L R := by
-- proof
  apply StatMech.Walls.bc72_GnForestNeighbours_of_singleHub ω L R a hxbox hsingle habdry hincid haoutside hcut hxne hainj

/--
[bc72_count_of_singleHub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_count_of_singleHub_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {x : Site d}
  {a : Fin 3 → Site d}
-- given
  (hxbox : x ∈ box d R)
  (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
  (habdry : ∀ i, a i ∈ vertexBoundary d R)
  (hincid : ∀ i, bc67_GnIncident ω L x (a i))
  (haoutside : ∀ i, a i ∉ bc61_boxAround d L x)
  (hcut : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (a i) (a j))
  (hxne : ∀ i, a i ≠ x)
  (hainj : Function.Injective a) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc72_count_of_singleHub ω L R a hxbox hsingle habdry hincid haoutside hcut hxne hainj

/--
[bc72_upperLines_arm_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_upperLines_arm_adjacent_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  ∃ a : Site 2, (bc72_quotGraph (openSubgraph 2 bc60_upperLines) (bc72_collapseBox L (0 : Site 2))).Adj 0 a := by
-- proof
  apply StatMech.Walls.bc72_upperLines_arm_adjacent hL

/--
[bc72_upperLines_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_upperLines_deg3_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  ∃ (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (hyS : (0 : Site 2) ∈ S) (_ : DecidableRel ((bc72_quotGraph (openSubgraph 2 bc60_upperLines) (bc72_collapseBox L (0 : Site 2))).induce S).Adj), 3 ≤ ((bc72_quotGraph (openSubgraph 2 bc60_upperLines) (bc72_collapseBox L (0 : Site 2))).induce S).degree ⟨0, hyS⟩ := by
-- proof
  apply StatMech.Walls.bc72_upperLines_deg3 hL

/--
[bc72_forestNeighbours_of_multiBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_forestNeighbours_of_multiBox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc72_MultiBoxForestOnQuot ω L R) :
-- imply
  bc71_GnForestNeighbours ω L R := by
-- proof
  apply StatMech.Walls.bc72_forestNeighbours_of_multiBox ω L R h

/--
[bc72_count_of_multiBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_count_of_multiBox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc72_MultiBoxForestOnQuot ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc72_count_of_multiBox ω L R h

/--
[bc72_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean)
-/
@[path]
private lemma bc72_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a : Site d), bc67_GnIncident ω L y a → a ∉ bc61_boxAround d L y → (bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).Adj y a) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d), bc67_IsGnTrifurcation ω L y → ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : y ∈ S) (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).Adj), 3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).degree ⟨y, hyS⟩) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc72_MultiBoxForestOnQuot ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc72_status


-- created on 2026-10-23
