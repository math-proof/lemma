import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.RootedForestPeelClose
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[rfp_root_arm_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_root_arm_obstruction_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {b : Site d → Site d}
  {rank : Site d → ℕ ×ₗ ℕ}
  {x₀ z : Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (hzbox : z ∈ box d n)
  (htriz : IsTrifurcation d ω z)
  (hne : x₀ ≠ z)
  (hconn : Connected d ω x₀ z)
  (hrank : rank x₀ ≠ rank z)
  (hpair : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x < rank y → Connected d (removeSite y ω) (b x) x ∧ ¬ Connected d (removeSite y ω) (b y) x)
  (hbeyond : Connected d (removeSite x₀ ω) (b x₀) z)
  (hcrossed : ¬ Connected d (removeSite z ω) (b x₀) x₀) :
-- imply
  False := by
-- proof
  apply StatMech.Percolation.rfp_root_arm_obstruction ω n hx0box htri0 hzbox htriz hne hconn hrank hpair hbeyond hcrossed

/--
[rfp_consistency_beyond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_consistency_beyond_eq
  {d : ℕ} :
-- imply
  Connected 1 (removeSite rfp_p0 rfp_ωpath) rfp_p2 rfp_p1 := by
-- proof
  apply StatMech.Percolation.rfp_consistency_beyond

/--
[rfp_path_noEdge_after_p1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_path_noEdge_after_p1_eq
  {d : ℕ}
  {a b : Site 1} :
-- imply
  ¬ (openSubgraph 1 (removeSite rfp_p1 rfp_ωpath)).Adj a b := by
-- proof
  apply StatMech.Percolation.rfp_path_noEdge_after_p1 a b

/--
[rfp_path_conn_eq_after_p1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_path_conn_eq_after_p1_eq
  {d : ℕ}
  {a b : Site 1}
-- given
  (h : Connected 1 (removeSite rfp_p1 rfp_ωpath) a b) :
-- imply
  a = b := by
-- proof
  apply StatMech.Percolation.rfp_path_conn_eq_after_p1 h

/--
[rfp_consistency_crossed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_consistency_crossed_eq
  {d : ℕ} :
-- imply
  ¬ Connected 1 (removeSite rfp_p1 rfp_ωpath) rfp_p2 rfp_p0 := by
-- proof
  apply StatMech.Percolation.rfp_consistency_crossed

/--
[rfp_armGeometry_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_armGeometry_consistent_eq
  {d : ℕ} :
-- imply
  ∃ (ω : ConfigSpace (Sym2 (Site 1))) (x₀ z w : Site 1), Connected 1 (removeSite x₀ ω) w z ∧ ¬ Connected 1 (removeSite z ω) w x₀ := by
-- proof
  apply StatMech.Percolation.rfp_armGeometry_consistent

/--
[rfp_not_rootedPrivateArm_of_clawArmGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_not_rootedPrivateArm_of_clawArmGeometry_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : rfp_ClawArmGeometry ω n) :
-- imply
  ¬ fcc_RootedPrivateArm ω n := by
-- proof
  apply StatMech.Percolation.rfp_not_rootedPrivateArm_of_clawArmGeometry ω n hgeo

/--
[rfp_clawArmGeometry_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_clawArmGeometry_of_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ : Site d}
  {y : Fin 3 → Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
  (hcross : ∀ b : Site d → Site d, (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite → ∃ i, Connected d (removeSite x₀ ω) (b x₀) (y i) ∧ ¬ Connected d (removeSite (y i) ω) (b x₀) x₀) :
-- imply
  rfp_ClawArmGeometry ω n := by
-- proof
  apply StatMech.Percolation.rfp_clawArmGeometry_of_claw ω n x₀ y hx0box htri0 hydata hcross

/--
[rfp_rootedPrivateArm_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_rootedPrivateArm_refutable_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : rfp_ClawArmGeometry ω n) :
-- imply
  ¬ fcc_RootedPrivateArm ω n := by
-- proof
  apply StatMech.Percolation.rfp_rootedPrivateArm_refutable ω n hgeo

/--
[rfp_rootedSingleCutSeparation_of_armDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_rootedSingleCutSeparation_of_armDivergence_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : rfp_RootedArmDivergence ω n) :
-- imply
  fcc_RootedSingleCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.rfp_rootedSingleCutSeparation_of_armDivergence ω n h

/--
[rfp_rootedArmDivergence_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_rootedArmDivergence_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  rfp_RootedArmDivergence ω n := by
-- proof
  apply StatMech.Percolation.rfp_rootedArmDivergence_of_noTrif ω n hno

/--
[rfp_rootedArmDivergence_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_rootedArmDivergence_of_twoTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
  {b : Site d → Site d}
-- given
  (hx0y0 : x₀ ≠ y₀)
  (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
  (hdeep : ¬ fsp_sameArm ω y₀ (b x₀) (b y₀)) :
-- imply
  rfp_RootedArmDivergence ω n := by
-- proof
  apply StatMech.Percolation.rfp_rootedArmDivergence_of_twoTrif ω n b hx0y0 htwo hbx0 hby0 hdeep

/--
[rfp_rootedArmDivergence_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_rootedArmDivergence_of_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ : Site d}
  {y : Fin 3 → Site d}
  {lx : Site d → Fin 3}
  {ly : Fin 3 → Site d → Fin 3}
  {b : Site d → Site d}
  {j₀ : Fin 3}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
  (hyinj : Function.Injective y)
  (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v → (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
  (hGstar : ∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w → (ly i w = 0 ↔ lx w ≠ i))
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
  (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hcy : ∀ i, lx (b (y i)) = i)
  (hcx : lx (b x₀) = j₀)
  (hcentral : ly j₀ (b x₀) ≠ ly j₀ (b (y j₀))) :
-- imply
  rfp_RootedArmDivergence ω n := by
-- proof
  apply StatMech.Percolation.rfp_rootedArmDivergence_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar hsingle b hbdata hcy hcx hcentral

/--
[rfp_rootedSpanningForest_of_coverArmDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_rootedSpanningForest_of_coverArmDivergence_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hcov : fcc_ThreeArmCover ω n)
  (hdiv : rfp_RootedArmDivergence ω n) :
-- imply
  stt_RootedSpanningForest ω n := by
-- proof
  apply StatMech.Percolation.rfp_rootedSpanningForest_of_coverArmDivergence ω n hcov hdiv

/--
[rfp_Tcount_le_boundary_of_coverArmDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_Tcount_le_boundary_of_coverArmDivergence_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcov : fcc_ThreeArmCover ω n)
  (hdiv : rfp_RootedArmDivergence ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.rfp_Tcount_le_boundary_of_coverArmDivergence ω n hn hcov hdiv

/--
[rfp_burton_keane_bernoulli_of_coverArmDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean)
-/
@[path]
private lemma rfp_burton_keane_bernoulli_of_coverArmDivergence_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hcov : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fcc_ThreeArmCover ω n)
  (hdiv : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → rfp_RootedArmDivergence ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.rfp_burton_keane_bernoulli_of_coverArmDivergence hd p hp1 hp0 hcov hdiv htrif


-- created on 2026-10-23
