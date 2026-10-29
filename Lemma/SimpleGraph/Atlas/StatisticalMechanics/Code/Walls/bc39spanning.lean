import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
open Set SimpleGraph Finset MeasureTheory StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc39_openEdge_removeSites_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean)
-/
@[path]
private lemma bc39_openEdge_removeSites_of_notMem_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : Site d}
-- given
  (hu : u ∉ S)
  (hv : v ∉ S)
  (h : (openSubgraph d ω).Adj u v) :
-- imply
  (openSubgraph d (removeSites S ω)).Adj u v := by
-- proof
  apply StatMech.Walls.bc39_openEdge_removeSites_of_notMem S ω hu hv h

/--
[bc39_connected_removeSites_of_walk_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean)
-/
@[path]
private lemma bc39_connected_removeSites_of_walk_avoids_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
  {p : (openSubgraph d ω).Walk a b}
-- given
  (hp : ∀ v ∈ p.support, v ∉ S) :
-- imply
  Connected d (removeSites S ω) a b := by
-- proof
  apply StatMech.Walls.bc39_connected_removeSites_of_walk_avoids S ω p hp

/--
[bc39_armAdj_edge_of_walk_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean)
-/
@[path]
private lemma bc39_armAdj_edge_of_walk_avoids_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {a b : Site d}
  {p : (openSubgraph d ω).Walk a b}
-- given
  (hab : a ≠ b)
  (hint : ∀ v ∈ p.support, v ∈ tfc_trifFinset ω n → v = a ∨ v = b) :
-- imply
  bc37_ArmAdjacent ω n a b := by
-- proof
  apply StatMech.Walls.bc39_armAdj_edge_of_walk_avoids ω n hab p hint

/--
[bc39_reach_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean)
-/
@[path]
private lemma bc39_reach_of_walk_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  ∀ (k : ℕ) {a b : Site d} (haT : a ∈ tfc_trifFinset ω n) (hbT : b ∈ tfc_trifFinset ω n) (p : (openSubgraph d ω).Walk a b), p.length ≤ k → (bc37_armAdjGraph ω n).Reachable ⟨a, haT⟩ ⟨b, hbT⟩ := by
-- proof
  apply StatMech.Walls.bc39_reach_of_walk ω n

/--
[bc39_armAdjSpanning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean)
-/
@[path]
private lemma bc39_armAdjSpanning_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc38_ArmAdjSpanning ω n := by
-- proof
  apply StatMech.Walls.bc39_armAdjSpanning ω n

/--
[bc39_armCutGeometry_false_of_armAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean)
-/
@[path]
private lemma bc39_armCutGeometry_false_of_armAdjacent_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {t s : Site d}
-- given
  (htbox : t ∈ box d n)
  (htri : IsTrifurcation d ω t)
  (hadj : bc37_ArmAdjacent ω n t s) :
-- imply
  ¬ bc38_ArmCutGeometry ω n := by
-- proof
  apply StatMech.Walls.bc39_armCutGeometry_false_of_armAdjacent ω n htbox htri hadj

/--
[bc39_armRealisation_of_cutGeometryFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean)
-/
@[path]
private lemma bc39_armRealisation_of_cutGeometryFixed_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc39_ArmCutGeometryFixed ω n) :
-- imply
  bc38_ArmRealisation ω n := by
-- proof
  apply StatMech.Walls.bc39_armRealisation_of_cutGeometryFixed ω n hgeo

/--
[bc39_parentFunneling_of_cutGeometryFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean)
-/
@[path]
private lemma bc39_parentFunneling_of_cutGeometryFixed_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc39_ArmCutGeometryFixed ω n) :
-- imply
  bc37_ParentFunneling ω n := by
-- proof
  apply StatMech.Walls.bc39_parentFunneling_of_cutGeometryFixed ω n hgeo

/--
[bc39_selfDownArm_of_cutGeometryFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean)
-/
@[path]
private lemma bc39_selfDownArm_of_cutGeometryFixed_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc39_ArmCutGeometryFixed ω n) :
-- imply
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc39_selfDownArm_of_cutGeometryFixed ω n hgeo

/--
[bc39_Tcount_le_boundary_of_cutGeometryFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean)
-/
@[path]
private lemma bc39_Tcount_le_boundary_of_cutGeometryFixed_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hgeo : bc39_ArmCutGeometryFixed ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc39_Tcount_le_boundary_of_cutGeometryFixed ω n hn hgeo

/--
[bc39_burton_keane_bernoulli_of_cutGeometryFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean)
-/
@[path]
private lemma bc39_burton_keane_bernoulli_of_cutGeometryFixed_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc39_ArmCutGeometryFixed ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc39_burton_keane_bernoulli_of_cutGeometryFixed hd p hp1 hp0 hgeo htrif

/--
[bc39_armCutGeometryFixed_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean)
-/
@[path]
private lemma bc39_armCutGeometryFixed_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc39_ArmCutGeometryFixed ω n := by
-- proof
  apply StatMech.Walls.bc39_armCutGeometryFixed_of_noTrif ω n hno

/--
[bc39_cutGeometryFixed_shadow_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean)
-/
@[path]
private lemma bc39_cutGeometryFixed_shadow_consistent_eq
  {d : ℕ}
  {parNode bpar bself : ℕ}
-- given
  (hnode : parNode ≠ bself)
  (hbpar : bpar ≠ bself)
  (F : ℕ → Prop)
  (hF : ∀ w, F w → w ≠ bself) :
-- imply
  ∃ up : ℕ → Prop, (¬ up bself ∧ up bpar) ∧ (¬ up bself ∧ up parNode) ∧ (∀ w, F w → up parNode ∧ up w) := by
-- proof
  apply StatMech.Walls.bc39_cutGeometryFixed_shadow_consistent parNode bpar bself hnode hbpar F hF

/--
[bc39_cutGeometryFixed_clauses_coexist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean)
-/
@[path]
private lemma bc39_cutGeometryFixed_clauses_coexist_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {b : Site d → Site d}
  {t s : Site d}
-- given
  (_hadj : bc37_ArmAdjacent ω n t s)
  (hloc : ¬ Connected d (removeSite t ω) (b t) (b s))
  (hself : ¬ Connected d (removeSite t ω) (b t) s)
  (hfun : ∀ x, x ≠ s → x ≠ t → Connected d (removeSite t ω) (b x) s) :
-- imply
  (¬ Connected d (removeSite t ω) (b t) (b s)) ∧ (¬ Connected d (removeSite t ω) (b t) s) ∧ (∀ x, x ≠ s → x ≠ t → Connected d (removeSite t ω) (b x) s) := by
-- proof
  apply StatMech.Walls.bc39_cutGeometryFixed_clauses_coexist ω n b _hadj hloc hself hfun


-- created on 2026-10-23
