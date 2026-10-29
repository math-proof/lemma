import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc30armforest.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc30_globalCutDownArmData_iff_rootedDownArmForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_globalCutDownArmData_iff_rootedDownArmForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ} :
-- imply
  bc30_GlobalCutDownArmData ω n rank ↔ bc29_RootedDownArmForest ω n rank := by
-- proof
  apply StatMech.Walls.bc30_globalCutDownArmData_iff_rootedDownArmForest ω n rank

/--
[bc30_bundledRootedDownArmForest_of_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_bundledRootedDownArmForest_of_data_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y)
  (hdata : bc30_GlobalCutDownArmData ω n rank) :
-- imply
  bc29_BundledRootedDownArmForest ω n := by
-- proof
  apply StatMech.Walls.bc30_bundledRootedDownArmForest_of_data ω n rank hinj hdata

/--
[bc30_bundled_iff_existsRankData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_bundled_iff_existsRankData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc29_BundledRootedDownArmForest ω n ↔ ∃ rank : Site d → ℕ ×ₗ ℕ, (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧ bc30_GlobalCutDownArmData ω n rank := by
-- proof
  apply StatMech.Walls.bc30_bundled_iff_existsRankData ω n

/--
[bc30_exists_depthRank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_exists_depthRank_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  ∃ rank : Site d → ℕ ×ₗ ℕ, ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y := by
-- proof
  apply StatMech.Walls.bc30_exists_depthRank ω n

/--
[bc30_bundledRootedDownArmForest_of_dataForDepthRank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_bundledRootedDownArmForest_of_dataForDepthRank_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : ∃ rank : Site d → ℕ ×ₗ ℕ, (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧ bc30_GlobalCutDownArmData ω n rank) :
-- imply
  bc29_BundledRootedDownArmForest ω n := by
-- proof
  apply StatMech.Walls.bc30_bundledRootedDownArmForest_of_dataForDepthRank ω n h

/--
[bc30_rootedArmDivergence_of_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_rootedArmDivergence_of_data_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y)
  (hdata : bc30_GlobalCutDownArmData ω n rank) :
-- imply
  rfp_RootedArmDivergence ω n := by
-- proof
  apply StatMech.Walls.bc30_rootedArmDivergence_of_data ω n rank hinj hdata

/--
[bc30_Tcount_le_boundary_of_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_Tcount_le_boundary_of_data_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (hn : 1 ≤ n)
  (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y)
  (hdata : bc30_GlobalCutDownArmData ω n rank) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc30_Tcount_le_boundary_of_data ω n hn rank hinj hdata

/--
[bc30_burton_keane_bernoulli_of_downArmData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_burton_keane_bernoulli_of_downArmData_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc29_BundledRootedDownArmForest ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc30_burton_keane_bernoulli_of_downArmData hd p hp1 hp0 hres htrif

/--
[bc30_globalCutDownArmData_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_globalCutDownArmData_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc30_GlobalCutDownArmData ω n rank := by
-- proof
  apply StatMech.Walls.bc30_globalCutDownArmData_of_noTrif ω n rank hno

/--
[bc30_globalCutDownArmData_of_uniqueTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_globalCutDownArmData_of_uniqueTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
  {x₀ a : Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (habox : a ∈ box d n)
  (haconn : Connected d ω x₀ a)
  (hainf : (cluster d (removeSites (tfc_trifFinset ω n) ω) a).Infinite)
  (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
-- imply
  bc30_GlobalCutDownArmData ω n rank := by
-- proof
  apply StatMech.Walls.bc30_globalCutDownArmData_of_uniqueTrif ω n rank hx0box htri0 habox haconn hainf huniq

/--
[bc30_globalCutDownArmData_of_threeChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_globalCutDownArmData_of_threeChain_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ m g : Site d}
  {b : Site d → Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (hmbox : m ∈ box d n)
  (hgbox : g ∈ box d n)
  (hx0m : x₀ ≠ m)
  (hx0g : x₀ ≠ g)
  (hmg : m ≠ g)
  (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b m)).Infinite)
  (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b g)).Infinite)
  (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
  (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
  (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
-- imply
  bc30_GlobalCutDownArmData ω n (fun z => if z = x₀ then toLex (0, 0) else if z = m then toLex (1, 0) else toLex (2, 0)) := by
-- proof
  apply StatMech.Walls.bc30_globalCutDownArmData_of_threeChain ω n b hx0box hmbox hgbox hx0m hx0g hmg hthree hbx0 hbm hbg hsxm hsxg hsmg

/--
[bc30_globalCutDownArmData_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_globalCutDownArmData_of_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ : Site d}
  {y : Fin 3 → Site d}
  {b : Site d → Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (hydata : ∀ i, y i ∈ box d n ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
  (hyinj : Function.Injective y)
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hby : ∀ i, b (y i) ∈ box d n ∧ Connected d ω (y i) (b (y i)) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b (y i))).Infinite)
  (hsx0 : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
  (hssib : ∀ i j : Fin 3, (j : ℕ) < i → ¬ Connected d (removeSite (y i) ω) (b (y i)) (b (y j))) :
-- imply
  bc30_GlobalCutDownArmData ω n (fun z => if z = x₀ then toLex (0, 0) else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0)) := by
-- proof
  apply StatMech.Walls.bc30_globalCutDownArmData_of_claw ω n x₀ y b hx0box hydata hyinj hsingle hbx0 hby hsx0 hssib

/--
[bc30_globalCutDownArmData_of_upArmFunneling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_globalCutDownArmData_of_upArmFunneling_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (h : bc30_UpArmFunneling ω n rank) :
-- imply
  bc30_GlobalCutDownArmData ω n rank := by
-- proof
  apply StatMech.Walls.bc30_globalCutDownArmData_of_upArmFunneling ω n rank h

/--
[bc30_bundledRootedDownArmForest_of_upArmFunneling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_bundledRootedDownArmForest_of_upArmFunneling_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y)
  (h : bc30_UpArmFunneling ω n rank) :
-- imply
  bc29_BundledRootedDownArmForest ω n := by
-- proof
  apply StatMech.Walls.bc30_bundledRootedDownArmForest_of_upArmFunneling ω n rank hinj h

/--
[bc30_upArmFunneling_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_upArmFunneling_of_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ : Site d}
  {y : Fin 3 → Site d}
  {b : Site d → Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (hydata : ∀ i, y i ∈ box d n ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
  (hyinj : Function.Injective y)
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hby : ∀ i, b (y i) ∈ box d n ∧ Connected d ω (y i) (b (y i)) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b (y i))).Infinite)
  (hx0down : ¬ Connected d (removeSite x₀ ω) (b x₀) x₀)
  (hsx0 : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
  (hsibfun : ∀ i j : Fin 3, (j : ℕ) < i → Connected d (removeSite (y i) ω) (b (y j)) (b x₀)) :
-- imply
  bc30_UpArmFunneling ω n (fun z => if z = x₀ then toLex (0, 0) else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0)) := by
-- proof
  apply StatMech.Walls.bc30_upArmFunneling_of_claw ω n x₀ y b hx0box hydata hyinj hsingle hbx0 hby hx0down hsx0 hsibfun

/--
[bc30_upArmFunneling_clauses_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_upArmFunneling_clauses_consistent_eq
  {d : ℕ} :
-- imply
  ∃ (ω : ConfigSpace (Sym2 (Site 1))) (y by' uy bx₁ bx₂ : Site 1), ¬ Connected 1 (removeSite y ω) by' uy ∧ Connected 1 (removeSite y ω) bx₁ uy ∧ ¬ Connected 1 (removeSite y ω) by' bx₂ ∧ Connected 1 (removeSite y ω) bx₂ uy := by
-- proof
  apply StatMech.Walls.bc30_upArmFunneling_clauses_consistent

/--
[bc30_upArmFunneling_of_threeChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean)
-/
@[path]
private lemma bc30_upArmFunneling_of_threeChain_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ m g : Site d}
  {b : Site d → Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (hmbox : m ∈ box d n)
  (hgbox : g ∈ box d n)
  (hx0m : x₀ ≠ m)
  (hx0g : x₀ ≠ g)
  (hmg : m ≠ g)
  (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b m)).Infinite)
  (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b g)).Infinite)
  (hx0down : ¬ Connected d (removeSite x₀ ω) (b x₀) x₀)
  (hmdown : ¬ Connected d (removeSite m ω) (b m) (b x₀))
  (hgdown : ¬ Connected d (removeSite g ω) (b g) (b m))
  (hfunx0g : Connected d (removeSite g ω) (b x₀) (b m)) :
-- imply
  bc30_UpArmFunneling ω n (fun z => if z = x₀ then toLex (0, 0) else if z = m then toLex (1, 0) else toLex (2, 0)) := by
-- proof
  apply StatMech.Walls.bc30_upArmFunneling_of_threeChain ω n b hx0box hmbox hgbox hx0m hx0g hmg hthree hbx0 hbm hbg hx0down hmdown hgdown hfunx0g


-- created on 2026-10-23
