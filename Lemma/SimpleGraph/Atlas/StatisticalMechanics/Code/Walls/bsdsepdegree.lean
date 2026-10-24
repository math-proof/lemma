import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bsdsepdegree
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bsd_boxes_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsdsepdegree.lean)
-/
@[path]
private lemma bsd_boxes_disjoint_eq
  {d : ℕ}
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hx : bc106_SeparatedCoarseTrif ω L x)
  (hy : bc106_SeparatedCoarseTrif ω L y)
  (hne : x ≠ y) :
-- imply
  Disjoint (bc61_boxAround d L x) (bc61_boxAround d L y) := by
-- proof
  apply StatMech.Walls.bsd_boxes_disjoint hx hy hne

/--
[bsd_deg3_free_per_trif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsdsepdegree.lean)
-/
@[path]
private lemma bsd_deg3_free_per_trif_eq
  {d : ℕ}
  {L : ℕ}
  {x : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hx : bc106_SeparatedCoarseTrif ω L x) :
-- imply
  ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : x ∈ S) (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L x)).induce S).Adj), 3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L x)).induce S).degree ⟨x, hyS⟩ := by
-- proof
  apply StatMech.Walls.bsd_deg3_free_per_trif hx

/--
[bsd_arm_tips_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsdsepdegree.lean)
-/
@[path]
private lemma bsd_arm_tips_of_separated_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {x : Site d}
  {arm : Fin 3 → Site d}
-- given
  (hR : 1 ≤ R)
  (harmbox : ∀ i, arm i ∈ box d R)
  (harmne : ∀ i, arm i ≠ x)
  (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite)
  (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j)) :
-- imply
  ∃ t : Fin 3 → Site d, (∀ i, t i ∈ vertexBoundary d R) ∧ (∀ i, (bc67_contractedLattice ω L x).Reachable (arm i) (t i)) ∧ (∀ i, t i ≠ x) ∧ (∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (t i) (t j)) := by
-- proof
  apply StatMech.Walls.bsd_arm_tips_of_separated ω L R hR arm harmbox harmne harminf harmsep

/--
[bsd_bc69_of_separated_singleStar_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsdsepdegree.lean)
-/
@[path]
private lemma bsd_bc69_of_separated_singleStar_route_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {x : Site d}
  {arm : Fin 3 → Site d}
-- given
  (hR : 1 ≤ R)
  (hxbox : x ∈ box d R)
  (hxsep : bc106_SeparatedCoarseTrif ω L x)
  (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
  (harmbox : ∀ i, arm i ∈ box d R)
  (harmne : ∀ i, arm i ≠ x)
  (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite)
  (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j))
  (hroute : ∀ a : Fin 3 → Site d, (∀ i, (bc67_contractedLattice ω L x).Reachable (arm i) (a i)) → (∀ i, a i ∈ vertexBoundary d R) → ∀ i j, i ≠ j → (bc67_contractedLattice ω L (a j)).Reachable x (a i)) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bsd_bc69_of_separated_singleStar_route ω L R hR arm hxbox hxsep hsingle harmbox harmne harminf harmsep hroute

/--
[bsd_collapse_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsdsepdegree.lean)
-/
@[path]
private lemma bsd_collapse_survives_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) := by
-- proof
  apply StatMech.Walls.bsd_collapse_survives L

/--
[bsd_bk_of_bc69_forall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsdsepdegree.lean)
-/
@[path]
private lemma bsd_bk_of_bc69_forall_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bsd_bk_of_bc69_forall p hp1 hp0 hdata

/--
[bsd_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsdsepdegree.lean)
-/
@[path]
private lemma bsd_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x y : Site d), bc106_SeparatedCoarseTrif ω L x → bc106_SeparatedCoarseTrif ω L y → x ≠ y → Disjoint (bc61_boxAround d L x) (bc61_boxAround d L y)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x : Site d), bc106_SeparatedCoarseTrif ω L x → ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : x ∈ S) (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L x)).induce S).Adj), 3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L x)).induce S).degree ⟨x, hyS⟩) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (x : Site d) (arm : Fin 3 → Site d), x ∈ box d R → bc106_SeparatedCoarseTrif ω L x → (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x) → (∀ i, arm i ∈ box d R) → (∀ i, arm i ≠ x) → (∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite) → (∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j)) → (∀ a : Fin 3 → Site d, (∀ i, (bc67_contractedLattice ω L x).Reachable (arm i) (a i)) → (∀ i, a i ∈ vertexBoundary d R) → ∀ i j, i ≠ j → (bc67_contractedLattice ω L (a j)).Reachable x (a i)) → bc69_Gn_globalForest ω L R) ∧ (∀ (L : ℕ), Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) := by
-- proof
  apply StatMech.Walls.bsd_status


-- created on 2026-10-23
