import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc38_exists_closer_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_exists_closer_neighbour_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {root v : V}
-- given
  (hr : G.Reachable root v)
  (hne : v ≠ root) :
-- imply
  ∃ u, G.Adj v u ∧ G.dist root u < G.dist root v := by
-- proof
  apply StatMech.Walls.bc38_exists_closer_neighbour G hr hne

/--
[bc38_parentTo_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_parentTo_spec_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {root : V → V}
  {v : V}
-- given
  (hne : v ≠ root v)
  (hr : G.Reachable (root v) v) :
-- imply
  G.Adj v (bc38_parentTo G root v) ∧ G.dist (root v) (bc38_parentTo G root v) < G.dist (root v) v := by
-- proof
  apply StatMech.Walls.bc38_parentTo_spec G root hne hr

/--
[bc38_exists_rootedArmForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_exists_rootedArmForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hspan : bc38_ArmAdjSpanning ω n) :
-- imply
  ∃ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧ (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x < rank y → bc37_ArmAdjacent ω n y (par y) ∧ rank (par y) < rank y) := by
-- proof
  apply StatMech.Walls.bc38_exists_rootedArmForest ω n hspan

/--
[bc38_armAdjAcyclic_iff_path_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_armAdjAcyclic_iff_path_unique_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc38_ArmAdjAcyclic ω n ↔ ∀ ⦃a b⦄ (p q : (bc37_armAdjGraph ω n).Path a b), p = q := by
-- proof
  apply StatMech.Walls.bc38_armAdjAcyclic_iff_path_unique ω n

/--
[bc38_unique_closer_neighbour_of_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_unique_closer_neighbour_of_acyclic_eq
  {d : ℕ}
  [DecidableEq V]
  {G : SimpleGraph V}
  {root v u₁ u₂ : V}
-- given
  (hac : G.IsAcyclic)
  (h0 : G.Adj v u₁)
  (h1 : G.Adj v u₂)
  (hd1 : G.dist root u₁ < G.dist root v)
  (hd2 : G.dist root u₂ < G.dist root v) :
-- imply
  u₁ = u₂ := by
-- proof
  apply StatMech.Walls.bc38_unique_closer_neighbour_of_acyclic G hac h0 h1 hd1 hd2

/--
[bc38_unique_armParent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_unique_armParent_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {root v u₁ u₂ : {x : Site d // x ∈ tfc_trifFinset ω n}}
-- given
  (hac : bc38_ArmAdjAcyclic ω n)
  (h0 : (bc37_armAdjGraph ω n).Adj v u₁)
  (h1 : (bc37_armAdjGraph ω n).Adj v u₂)
  (hd1 : (bc37_armAdjGraph ω n).dist root u₁ < (bc37_armAdjGraph ω n).dist root v)
  (hd2 : (bc37_armAdjGraph ω n).dist root u₂ < (bc37_armAdjGraph ω n).dist root v) :
-- imply
  u₁ = u₂ := by
-- proof
  apply StatMech.Walls.bc38_unique_armParent ω n hac h0 h1 hd1 hd2

/--
[bc38_parentFunneling_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_parentFunneling_of_residues_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hspan : bc38_ArmAdjSpanning ω n)
  (hreal : bc38_ArmRealisation ω n) :
-- imply
  bc37_ParentFunneling ω n := by
-- proof
  apply StatMech.Walls.bc38_parentFunneling_of_residues ω n hspan hreal

/--
[bc38_selfDownArm_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_selfDownArm_of_residues_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hspan : bc38_ArmAdjSpanning ω n)
  (hreal : bc38_ArmRealisation ω n) :
-- imply
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc38_selfDownArm_of_residues ω n hspan hreal

/--
[bc38_Tcount_le_boundary_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_Tcount_le_boundary_of_residues_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hspan : bc38_ArmAdjSpanning ω n)
  (hreal : bc38_ArmRealisation ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc38_Tcount_le_boundary_of_residues ω n hn hspan hreal

/--
[bc38_burton_keane_bernoulli_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_burton_keane_bernoulli_of_residues_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hspan : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc38_ArmAdjSpanning ω n)
  (hreal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc38_ArmRealisation ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc38_burton_keane_bernoulli_of_residues hd p hp1 hp0 hspan hreal htrif

/--
[bc38_armAdjSpanning_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_armAdjSpanning_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc38_ArmAdjSpanning ω n := by
-- proof
  apply StatMech.Walls.bc38_armAdjSpanning_of_noTrif ω n hno

/--
[bc38_armAdjSpanning_of_threePath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_armAdjSpanning_of_threePath_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ m g : Site d}
-- given
  (hx0m : x₀ ≠ m)
  (hx0g : x₀ ≠ g)
  (hmg : m ≠ g)
  (hthree : ∀ x, x ∈ tfc_trifFinset ω n → x = x₀ ∨ x = m ∨ x = g)
  (hx0T : x₀ ∈ tfc_trifFinset ω n)
  (hmT : m ∈ tfc_trifFinset ω n)
  (hgT : g ∈ tfc_trifFinset ω n)
  (hadj_x0m : bc37_ArmAdjacent ω n x₀ m)
  (hadj_mg : bc37_ArmAdjacent ω n m g) :
-- imply
  bc38_ArmAdjSpanning ω n := by
-- proof
  apply StatMech.Walls.bc38_armAdjSpanning_of_threePath ω n hx0m hx0g hmg hthree hx0T hmT hgT hadj_x0m hadj_mg

/--
[bc38_armRealisation_of_cutGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_armRealisation_of_cutGeometry_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc38_ArmCutGeometry ω n) :
-- imply
  bc38_ArmRealisation ω n := by
-- proof
  apply StatMech.Walls.bc38_armRealisation_of_cutGeometry ω n hgeo

/--
[bc38_armCutGeometry_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_armCutGeometry_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc38_ArmCutGeometry ω n := by
-- proof
  apply StatMech.Walls.bc38_armCutGeometry_of_noTrif ω n hno

/--
[bc38_armRealisation_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_armRealisation_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc38_ArmRealisation ω n := by
-- proof
  apply StatMech.Walls.bc38_armRealisation_of_noTrif ω n hno

/--
[bc38_cutGeometry_shadow_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_cutGeometry_shadow_consistent_eq
  {d : ℕ}
  {parNode bpar bself : ℕ}
-- given
  (hnode : parNode ≠ bself)
  (hbpar : bpar ≠ bself) :
-- imply
  ∃ up : ℕ → Prop, (¬ up bself ∧ up bpar) ∧ (¬ up bself ∧ up parNode) ∧ (∀ w, w ≠ parNode → w ≠ bself → up parNode ∧ up w) := by
-- proof
  apply StatMech.Walls.bc38_cutGeometry_shadow_consistent parNode bpar bself hnode hbpar

/--
[bc38_parentFunneling_of_spanning_cutGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_parentFunneling_of_spanning_cutGeometry_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hspan : bc38_ArmAdjSpanning ω n)
  (hgeo : bc38_ArmCutGeometry ω n) :
-- imply
  bc37_ParentFunneling ω n := by
-- proof
  apply StatMech.Walls.bc38_parentFunneling_of_spanning_cutGeometry ω n hspan hgeo

/--
[bc38_selfDownArm_of_spanning_cutGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_selfDownArm_of_spanning_cutGeometry_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hspan : bc38_ArmAdjSpanning ω n)
  (hgeo : bc38_ArmCutGeometry ω n) :
-- imply
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc38_selfDownArm_of_spanning_cutGeometry ω n hspan hgeo

/--
[bc38_Tcount_le_boundary_of_spanning_cutGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_Tcount_le_boundary_of_spanning_cutGeometry_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hspan : bc38_ArmAdjSpanning ω n)
  (hgeo : bc38_ArmCutGeometry ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc38_Tcount_le_boundary_of_spanning_cutGeometry ω n hn hspan hgeo

/--
[bc38_burton_keane_bernoulli_of_spanning_cutGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean)
-/
@[path]
private lemma bc38_burton_keane_bernoulli_of_spanning_cutGeometry_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hspan : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc38_ArmAdjSpanning ω n)
  (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc38_ArmCutGeometry ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc38_burton_keane_bernoulli_of_spanning_cutGeometry hd p hp1 hp0 hspan hgeo htrif


-- created on 2026-10-23
