import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.ForestAcyclicityClose
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[fac_singleCut_of_globalCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestAcyclicityClose.lean)
-/
@[path]
private lemma fac_singleCut_of_globalCut_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {z u v : Site d}
-- given
  (hzT : z ∈ T)
  (h : Connected d (removeSites T ω) u v) :
-- imply
  Connected d (removeSite z ω) u v := by
-- proof
  apply StatMech.Percolation.fac_singleCut_of_globalCut T ω hzT h

/--
[fac_globalDisc_of_singleDisc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestAcyclicityClose.lean)
-/
@[path]
private lemma fac_globalDisc_of_singleDisc_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {z u v : Site d}
-- given
  (hzT : z ∈ T)
  (h : ¬ Connected d (removeSite z ω) u v) :
-- imply
  ¬ Connected d (removeSites T ω) u v := by
-- proof
  apply StatMech.Percolation.fac_globalDisc_of_singleDisc T ω hzT h

/--
[fac_trif_mem_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestAcyclicityClose.lean)
-/
@[path]
private lemma fac_trif_mem_finset_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
-- given
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x) :
-- imply
  x ∈ tfc_trifFinset ω n := by
-- proof
  apply StatMech.Percolation.fac_trif_mem_finset ω n hxbox htri

/--
[fac_globalSep_of_eitherCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestAcyclicityClose.lean)
-/
@[path]
private lemma fac_globalSep_of_eitherCut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x y u v : Site d}
-- given
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x)
  (hybox : y ∈ box d n)
  (htriy : IsTrifurcation d ω y)
  (h : ¬ Connected d (removeSite x ω) u v ∨ ¬ Connected d (removeSite y ω) u v) :
-- imply
  ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) u v := by
-- proof
  apply StatMech.Percolation.fac_globalSep_of_eitherCut ω n hxbox htri hybox htriy h

/--
[fac_globalForestArms_of_pairwiseCutSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestAcyclicityClose.lean)
-/
@[path]
private lemma fac_globalForestArms_of_pairwiseCutSeparation_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : fac_PairwiseCutSeparation ω n) :
-- imply
  aed_GlobalForestArms ω n := by
-- proof
  apply StatMech.Percolation.fac_globalForestArms_of_pairwiseCutSeparation ω n h

/--
[fac_pairwiseCutSeparation_of_privateArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestAcyclicityClose.lean)
-/
@[path]
private lemma fac_pairwiseCutSeparation_of_privateArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : daepf_PrivateArm ω n) :
-- imply
  fac_PairwiseCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.fac_pairwiseCutSeparation_of_privateArm ω n h

/--
[fac_globalForestArms_of_privateArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestAcyclicityClose.lean)
-/
@[path]
private lemma fac_globalForestArms_of_privateArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : daepf_PrivateArm ω n) :
-- imply
  aed_GlobalForestArms ω n := by
-- proof
  apply StatMech.Percolation.fac_globalForestArms_of_privateArm ω n h

/--
[fac_pairwiseCutSeparation_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestAcyclicityClose.lean)
-/
@[path]
private lemma fac_pairwiseCutSeparation_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  fac_PairwiseCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.fac_pairwiseCutSeparation_of_noTrif ω n hno

/--
[fac_pairwiseCutSeparation_of_uniqueTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestAcyclicityClose.lean)
-/
@[path]
private lemma fac_pairwiseCutSeparation_of_uniqueTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ a : Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (habox : a ∈ box d n)
  (haconn : Connected d ω x₀ a)
  (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
  (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
-- imply
  fac_PairwiseCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.fac_pairwiseCutSeparation_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq

/--
[fac_pairwiseCutSeparation_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestAcyclicityClose.lean)
-/
@[path]
private lemma fac_pairwiseCutSeparation_of_twoTrif_eq
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
  (hsep_x : ¬ Connected d (removeSite x₀ ω) (b x₀) (b y₀))
  (hsep_y : ¬ Connected d (removeSite y₀ ω) (b y₀) (b x₀)) :
-- imply
  fac_PairwiseCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.fac_pairwiseCutSeparation_of_twoTrif ω n b hx0y0 htwo hbx0 hby0 hsep_x hsep_y

/--
[fac_pairwiseCutSeparation_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestAcyclicityClose.lean)
-/
@[path]
private lemma fac_pairwiseCutSeparation_of_claw_eq
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
  (_hyinj : Function.Injective y)
  (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v → (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
  (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v → (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
  (hGstar : ∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w → (ly i w = 0 ↔ lx w ≠ i))
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
  (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hcy : ∀ i, lx (b (y i)) = i)
  (hcx : lx (b x₀) = j₀)
  (hcentral : ly j₀ (b x₀) ≠ ly j₀ (b (y j₀))) :
-- imply
  fac_PairwiseCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.fac_pairwiseCutSeparation_of_claw ω n x₀ y lx ly hx0box htri0 hydata _hyinj hlxf hlyf hGstar hsingle b hbdata hcy hcx hcentral

/--
[fac_Tcount_le_boundary_of_pairwiseCutSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestAcyclicityClose.lean)
-/
@[path]
private lemma fac_Tcount_le_boundary_of_pairwiseCutSeparation_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : fac_PairwiseCutSeparation ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.fac_Tcount_le_boundary_of_pairwiseCutSeparation ω n hn h

/--
[fac_burton_keane_bernoulli_of_pairwiseCutSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestAcyclicityClose.lean)
-/
@[path]
private lemma fac_burton_keane_bernoulli_of_pairwiseCutSeparation_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fac_PairwiseCutSeparation ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.fac_burton_keane_bernoulli_of_pairwiseCutSeparation hd p hp1 hp0 hres htrif


-- created on 2026-10-23
