import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.ForestColouringClose2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[fcc_notSameArm_of_singleCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_notSameArm_of_singleCut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y u v : Site d}
-- given
  (hyu : Connected d ω y u)
  (hneu : y ≠ u)
  (hyv : Connected d ω y v)
  (hnev : y ≠ v)
  (hsep : ¬ Connected d (removeSite y ω) u v) :
-- imply
  ¬ fsp_sameArm ω y u v := by
-- proof
  apply StatMech.Percolation.fcc_notSameArm_of_singleCut ω hyu hneu hyv hnev hsep

/--
[fcc_removeSite_self_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_removeSite_self_eq_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y v : Site d}
-- given
  (h : Connected d (removeSite y ω) y v) :
-- imply
  v = y := by
-- proof
  apply StatMech.Percolation.fcc_removeSite_self_eq ω h

/--
[fcc_two_distinct_arms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_two_distinct_arms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d}
-- given
  (htri : IsTrifurcation d ω y) :
-- imply
  ∃ u v, (Connected d ω y u ∧ y ≠ u) ∧ (Connected d ω y v ∧ y ≠ v) ∧ ¬ fsp_sameArm ω y u v := by
-- proof
  apply StatMech.Percolation.fcc_two_distinct_arms ω htri

/--
[fcc_threeArmCover_of_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_threeArmCover_of_faithful_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {c : Site d → Site d → Fin 3}
-- given
  (hcolor : ∀ y, y ∈ box d n → IsTrifurcation d ω y → ∀ u v, Connected d ω y u → y ≠ u → Connected d ω y v → y ≠ v → (c y u = c y v ↔ fsp_sameArm ω y u v)) :
-- imply
  fcc_ThreeArmCover ω n := by
-- proof
  apply StatMech.Percolation.fcc_threeArmCover_of_faithful ω n c hcolor

/--
[fcc_rootedSpanningForest_of_coverSep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_rootedSpanningForest_of_coverSep_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hcov : fcc_ThreeArmCover ω n)
  (hsep : fcc_RootedSingleCutSeparation ω n) :
-- imply
  stt_RootedSpanningForest ω n := by
-- proof
  apply StatMech.Percolation.fcc_rootedSpanningForest_of_coverSep ω n hcov hsep

/--
[fcc_threeArmCover_of_rootedSpanningForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_threeArmCover_of_rootedSpanningForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : stt_RootedSpanningForest ω n) :
-- imply
  fcc_ThreeArmCover ω n := by
-- proof
  apply StatMech.Percolation.fcc_threeArmCover_of_rootedSpanningForest ω n h

/--
[fcc_rootedSingleCutSeparation_of_rootedSpanningForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_rootedSingleCutSeparation_of_rootedSpanningForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : stt_RootedSpanningForest ω n) :
-- imply
  fcc_RootedSingleCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.fcc_rootedSingleCutSeparation_of_rootedSpanningForest ω n h

/--
[fcc_rootedSpanningForest_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_rootedSpanningForest_iff_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  stt_RootedSpanningForest ω n ↔ (fcc_ThreeArmCover ω n ∧ fcc_RootedSingleCutSeparation ω n) := by
-- proof
  apply StatMech.Percolation.fcc_rootedSpanningForest_iff ω n

/--
[fcc_rootedSingleCutSeparation_of_rootedPrivateArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_rootedSingleCutSeparation_of_rootedPrivateArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : fcc_RootedPrivateArm ω n) :
-- imply
  fcc_RootedSingleCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.fcc_rootedSingleCutSeparation_of_rootedPrivateArm ω n h

/--
[fcc_rootedSpanningForest_of_armsPrivate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_rootedSpanningForest_of_armsPrivate_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hcov : fcc_ThreeArmCover ω n)
  (hpriv : fcc_RootedPrivateArm ω n) :
-- imply
  stt_RootedSpanningForest ω n := by
-- proof
  apply StatMech.Percolation.fcc_rootedSpanningForest_of_armsPrivate ω n hcov hpriv

/--
[fcc_rootedSpanningForest_of_coverPrivate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_rootedSpanningForest_of_coverPrivate_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hcov : fcc_ThreeArmCover ω n)
  (hpriv : fcc_RootedPrivateArm ω n) :
-- imply
  stt_RootedSpanningForest ω n := by
-- proof
  apply StatMech.Percolation.fcc_rootedSpanningForest_of_coverPrivate ω n hcov hpriv

/--
[fcc_Tcount_le_boundary_of_armsPrivate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_Tcount_le_boundary_of_armsPrivate_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcov : fcc_ThreeArmCover ω n)
  (hpriv : fcc_RootedPrivateArm ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.fcc_Tcount_le_boundary_of_armsPrivate ω n hn hcov hpriv

/--
[fcc_burton_keane_bernoulli_of_armsPrivate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_burton_keane_bernoulli_of_armsPrivate_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hcov : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fcc_ThreeArmCover ω n)
  (hpriv : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fcc_RootedPrivateArm ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.fcc_burton_keane_bernoulli_of_armsPrivate hd p hp1 hp0 hcov hpriv htrif

/--
[fcc_threeArmCover_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_threeArmCover_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  fcc_ThreeArmCover ω n := by
-- proof
  apply StatMech.Percolation.fcc_threeArmCover_of_noTrif ω n hno

/--
[fcc_threeArmCover_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_threeArmCover_of_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ : Site d}
  {y : Fin 3 → Site d}
  {lx : Site d → Fin 3}
  {ly : Fin 3 → Site d → Fin 3}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
  (hyinj : Function.Injective y)
  (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v → (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
  (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v → (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i) :
-- imply
  fcc_ThreeArmCover ω n := by
-- proof
  apply StatMech.Percolation.fcc_threeArmCover_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlxf hlyf hsingle

/--
[fcc_rootedPrivateArm_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_rootedPrivateArm_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  fcc_RootedPrivateArm ω n := by
-- proof
  apply StatMech.Percolation.fcc_rootedPrivateArm_of_noTrif ω n hno

/--
[fcc_rootedPrivateArm_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_rootedPrivateArm_of_twoTrif_eq
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
  (hfar : Connected d (removeSite y₀ ω) (b x₀) x₀)
  (hpriv : ¬ Connected d (removeSite y₀ ω) (b y₀) x₀) :
-- imply
  fcc_RootedPrivateArm ω n := by
-- proof
  apply StatMech.Percolation.fcc_rootedPrivateArm_of_twoTrif ω n b hx0y0 htwo hbx0 hby0 hfar hpriv

/--
[fcc_rootedSingleCutSeparation_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_rootedSingleCutSeparation_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  fcc_RootedSingleCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.fcc_rootedSingleCutSeparation_of_noTrif ω n hno

/--
[fcc_rootedSingleCutSeparation_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_rootedSingleCutSeparation_of_claw_eq
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
  fcc_RootedSingleCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.fcc_rootedSingleCutSeparation_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar hsingle b hbdata hcy hcx hcentral

/--
[fcc_rootedSpanningForest_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean)
-/
@[path]
private lemma fcc_rootedSpanningForest_of_claw_eq
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
  (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v → (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
  (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v → (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
  (hGstar : ∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w → (ly i w = 0 ↔ lx w ≠ i))
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
  (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hcy : ∀ i, lx (b (y i)) = i)
  (hcx : lx (b x₀) = j₀)
  (hcentral : ly j₀ (b x₀) ≠ ly j₀ (b (y j₀))) :
-- imply
  stt_RootedSpanningForest ω n := by
-- proof
  apply StatMech.Percolation.fcc_rootedSpanningForest_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlxf hlyf hGstar hsingle b hbdata hcy hcx hcentral


-- created on 2026-10-23
