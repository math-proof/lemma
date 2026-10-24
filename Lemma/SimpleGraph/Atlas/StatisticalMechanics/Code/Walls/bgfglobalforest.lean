import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bgfglobalforest
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bgf_targets_sep_of_arms_sep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfglobalforest.lean)
-/
@[path]
private lemma bgf_targets_sep_of_arms_sep_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
  {aᵢ aⱼ zᵢ zⱼ : Site d}
-- given
  (hri : (bc67_contractedLattice ω L y).Reachable aᵢ zᵢ)
  (hrj : (bc67_contractedLattice ω L y).Reachable aⱼ zⱼ)
  (hcut : ¬ (bc67_contractedLattice ω L y).Reachable aᵢ aⱼ) :
-- imply
  ¬ (bc67_contractedLattice ω L y).Reachable zᵢ zⱼ := by
-- proof
  apply StatMech.Walls.bgf_targets_sep_of_arms_sep ω L y hri hrj hcut

/--
[bgf_three_targets_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfglobalforest.lean)
-/
@[path]
private lemma bgf_three_targets_separated_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
  {a₁ a₂ a₃ z₁ z₂ z₃ : Site d}
-- given
  (hr₁ : (bc67_contractedLattice ω L y).Reachable a₁ z₁)
  (hr₂ : (bc67_contractedLattice ω L y).Reachable a₂ z₂)
  (hr₃ : (bc67_contractedLattice ω L y).Reachable a₃ z₃)
  (hc₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂)
  (hc₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃)
  (hc₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) :
-- imply
  ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃ := by
-- proof
  apply StatMech.Walls.bgf_three_targets_separated ω L y hr₁ hr₂ hr₃ hc₁₂ hc₁₃ hc₂₃

/--
[bgf_boundary_targets_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfglobalforest.lean)
-/
@[path]
private lemma bgf_boundary_targets_distinct_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
  {z₁ z₂ z₃ : Site d}
-- given
  (hs₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂)
  (hs₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃)
  (hs₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃) :
-- imply
  z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃ := by
-- proof
  apply StatMech.Walls.bgf_boundary_targets_distinct ω L y hs₁₂ hs₁₃ hs₂₃

/--
[bgf_gnTrif_three_boundary_targets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfglobalforest.lean)
-/
@[path]
private lemma bgf_gnTrif_three_boundary_targets_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y a₁ a₂ a₃ : Site d}
-- given
  (hR : 1 ≤ R)
  (hb₁ : a₁ ∈ box d R)
  (hb₂ : a₂ ∈ box d R)
  (hb₃ : a₃ ∈ box d R)
  (hi₁ : (cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite)
  (hi₂ : (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite)
  (hi₃ : (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite)
  (hc₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂)
  (hc₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃)
  (hc₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) :
-- imply
  ∃ z₁ z₂ z₃ : Site d, (z₁ ∈ vertexBoundary d R ∧ z₂ ∈ vertexBoundary d R ∧ z₃ ∈ vertexBoundary d R) ∧ ((bc67_contractedLattice ω L y).Reachable a₁ z₁ ∧ (bc67_contractedLattice ω L y).Reachable a₂ z₂ ∧ (bc67_contractedLattice ω L y).Reachable a₃ z₃) ∧ (¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃) ∧ (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
-- proof
  apply StatMech.Walls.bgf_gnTrif_three_boundary_targets ω L R hR y a₁ a₂ a₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hc₁₂ hc₁₃ hc₂₃

/--
[bgf_arm_boundary_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfglobalforest.lean)
-/
@[path]
private lemma bgf_arm_boundary_separated_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y : Site d}
-- given
  (hR : 1 ≤ R)
  (htri : bc67_IsGnTrifurcation ω L y)
  (harmbox : ∀ a, (bc67_GnIncident ω L y a) → (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite → a ∈ box d R) :
-- imply
  ∃ z₁ z₂ z₃ : Site d, (z₁ ∈ vertexBoundary d R ∧ z₂ ∈ vertexBoundary d R ∧ z₃ ∈ vertexBoundary d R) ∧ (¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃) ∧ (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
-- proof
  apply StatMech.Walls.bgf_arm_boundary_separated ω L R hR y htri harmbox

/--
[bgf_HubBoundaryArms_within_hub_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfglobalforest.lean)
-/
@[path]
private lemma bgf_HubBoundaryArms_within_hub_free_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
-- given
  (hwit : bgf_WithinHubTips ω L R arm) :
-- imply
  (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ j, arm y j ∈ vertexBoundary d R) ∧ (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ j k, arm y j = arm y k → j = k) := by
-- proof
  apply StatMech.Walls.bgf_HubBoundaryArms_within_hub_free ω L R hwit

/--
[bgf_perNode_cut_needs_common_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfglobalforest.lean)
-/
@[path]
private lemma bgf_perNode_cut_needs_common_carrier_eq
  {d : ℕ} :
-- imply
  ((SimpleGraph.fromEdgeSet {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet (0 : Fin 5)).Reachable 2 4 := by
-- proof
  apply StatMech.Walls.bgf_perNode_cut_needs_common_carrier

/--
[bgf_globalForest_of_withinHub_and_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfglobalforest.lean)
-/
@[path]
private lemma bgf_globalForest_of_withinHub_and_cross_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {arm : Site d → Fin 3 → Site d}
  {base : ↑(bc122_carrier ω L R arm)}
-- given
  (hwit : bgf_WithinHubTips ω L R arm)
  (hcross : (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ∀ j k, arm y j = arm z k → y = z ∧ j = k) ∧ (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ∀ j, arm y j ≠ z))
  (hFmin : ∀ (F : SimpleGraph (↑(bc122_carrier ω L R arm) : Type)) [DecidableRel F.Adj], F ≤ bc122_starGraph ω L R arm → F.IsAcyclic → (∀ v : (↑(bc122_carrier ω L R arm) : Type), F.degree v = 1 → bc121_Protected ω L R (bc122_ιU ω L R arm base) v) → (∀ a b : (↑(bc122_carrier ω L R arm) : Type), bc121_Protected ω L R (bc122_ιU ω L R arm base) a → bc121_Protected ω L R (bc122_ιU ω L R arm base) b → (bc122_starGraph ω L R arm).Reachable a b → F.Reachable a b) → ∀ v : (↑(bc122_carrier ω L R arm) : Type), 1 ≤ F.degree v) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bgf_globalForest_of_withinHub_and_cross ω L R hwit hcross base hFmin

/--
[bgf_withinHubTips_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfglobalforest.lean)
-/
@[path]
private lemma bgf_withinHubTips_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
-- imply
  bgf_WithinHubTips ω L R (fun _ _ => (0 : Site d)) := by
-- proof
  apply StatMech.Walls.bgf_withinHubTips_nonvacuous ω L R hno

/--
[bgf_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfglobalforest.lean)
-/
@[path]
private lemma bgf_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) (z₁ z₂ z₃ : Site d), ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂ → ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃ → ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃ → z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (arm : Site d → Fin 3 → Site d), bgf_WithinHubTips ω L R arm → (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ j, arm y j ∈ vertexBoundary d R) ∧ (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ j k, arm y j = arm y k → j = k)) ∧ (((SimpleGraph.fromEdgeSet {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet (0 : Fin 5)).Reachable 2 4) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (arm : Site d → Fin 3 → Site d), bgf_WithinHubTips ω L R arm → True) := by
-- proof
  apply StatMech.Walls.bgf_status


-- created on 2026-10-23
