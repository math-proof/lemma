import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.PrivateArmProve
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[pap_meets_at_most_one_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PrivateArmProve.lean)
-/
@[path]
private lemma pap_meets_at_most_one_branch_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a₁ a₂ a₃ : Site d}
  {v : Site d}
-- given
  (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
  (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
  (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
-- imply
  ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₂ v) ∧ ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₃ v) ∧ ¬ (Connected d (removeSite x ω) a₂ v ∧ Connected d (removeSite x ω) a₃ v) := by
-- proof
  apply StatMech.Percolation.pap_meets_at_most_one_branch ω hd12 hd13 hd23 v

/--
[pap_two_branches_avoid_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PrivateArmProve.lean)
-/
@[path]
private lemma pap_two_branches_avoid_vertex_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a₁ a₂ a₃ : Site d}
  {v : Site d}
-- given
  (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
  (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
  (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
-- imply
  (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₂ v) ∨ (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₃ v) ∨ (¬ Connected d (removeSite x ω) a₂ v ∧ ¬ Connected d (removeSite x ω) a₃ v) := by
-- proof
  apply StatMech.Percolation.pap_two_branches_avoid_vertex ω hd12 hd13 hd23 v

/--
[pap_exists_private_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PrivateArmProve.lean)
-/
@[path]
private lemma pap_exists_private_branch_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a₁ a₂ a₃ : Site d}
  {v : Site d}
-- given
  (ha1box : a₁ ∈ box d n)
  (ha2box : a₂ ∈ box d n)
  (_ha3box : a₃ ∈ box d n)
  (hc1 : Connected d ω x a₁)
  (hc2 : Connected d ω x a₂)
  (_hc3 : Connected d ω x a₃)
  (hi1 : (cluster d (removeSite x ω) a₁).Infinite)
  (hi2 : (cluster d (removeSite x ω) a₂).Infinite)
  (_hi3 : (cluster d (removeSite x ω) a₃).Infinite)
  (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
  (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
  (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
-- imply
  ∃ a, a ∈ box d n ∧ Connected d ω x a ∧ (cluster d (removeSite x ω) a).Infinite ∧ ¬ Connected d (removeSite x ω) a v := by
-- proof
  apply StatMech.Percolation.pap_exists_private_branch ω n ha1box ha2box _ha3box hc1 hc2 _hc3 hi1 hi2 _hi3 hd12 hd13 hd23 v

/--
[pap_adj_removeSite_of_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PrivateArmProve.lean)
-/
@[path]
private lemma pap_adj_removeSite_of_avoid_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x u w : Site d}
-- given
  (hu : u ≠ x)
  (hw : w ≠ x)
  (hadj : (openSubgraph d ω).Adj u w) :
-- imply
  (openSubgraph d (removeSite x ω)).Adj u w := by
-- proof
  apply StatMech.Percolation.pap_adj_removeSite_of_avoid ω hu hw hadj

/--
[pap_connected_removeSite_of_walk_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PrivateArmProve.lean)
-/
@[path]
private lemma pap_connected_removeSite_of_walk_avoid_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {u w : Site d}
  {p : (openSubgraph d ω).Walk u w}
-- given
  (hx : x ∉ p.support) :
-- imply
  Connected d (removeSite x ω) u w := by
-- proof
  apply StatMech.Percolation.pap_connected_removeSite_of_walk_avoid ω x p hx

/--
[pap_far_of_avoiding_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PrivateArmProve.lean)
-/
@[path]
private lemma pap_far_of_avoiding_path_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y by_ : Site d}
  {p : (openSubgraph d ω).Walk by_ y}
-- given
  (hx : x ∉ p.support) :
-- imply
  Connected d (removeSite x ω) by_ y := by
-- proof
  apply StatMech.Percolation.pap_far_of_avoiding_path ω p hx

/--
[pap_privateArm_of_coherentSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PrivateArmProve.lean)
-/
@[path]
private lemma pap_privateArm_of_coherentSelector_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : pap_CoherentSelector ω n) :
-- imply
  daepf_PrivateArm ω n := by
-- proof
  apply StatMech.Percolation.pap_privateArm_of_coherentSelector ω n h

/--
[pap_coherentSelector_iff_privateArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PrivateArmProve.lean)
-/
@[path]
private lemma pap_coherentSelector_iff_privateArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  pap_CoherentSelector ω n ↔ daepf_PrivateArm ω n := by
-- proof
  apply StatMech.Percolation.pap_coherentSelector_iff_privateArm ω n

/--
[pap_coherentSelector_of_twoTrif_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PrivateArmProve.lean)
-/
@[path]
private lemma pap_coherentSelector_of_twoTrif_local_eq
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
  (hpriv_xy : ¬ Connected d (removeSite x₀ ω) (b x₀) y₀)
  (hfar_xy : Connected d (removeSite x₀ ω) (b y₀) y₀)
  (hpriv_yx : ¬ Connected d (removeSite y₀ ω) (b y₀) x₀)
  (hfar_yx : Connected d (removeSite y₀ ω) (b x₀) x₀) :
-- imply
  pap_CoherentSelector ω n := by
-- proof
  apply StatMech.Percolation.pap_coherentSelector_of_twoTrif_local ω n b hx0y0 htwo hbx0 hby0 hpriv_xy hfar_xy hpriv_yx hfar_yx

/--
[pap_coherentSelector_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PrivateArmProve.lean)
-/
@[path]
private lemma pap_coherentSelector_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  pap_CoherentSelector ω n := by
-- proof
  apply StatMech.Percolation.pap_coherentSelector_of_noTrif ω n hno

/--
[pap_coherentSelector_of_uniqueTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PrivateArmProve.lean)
-/
@[path]
private lemma pap_coherentSelector_of_uniqueTrif_eq
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
  pap_CoherentSelector ω n := by
-- proof
  apply StatMech.Percolation.pap_coherentSelector_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq

/--
[pap_Tcount_le_boundary_of_coherentSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PrivateArmProve.lean)
-/
@[path]
private lemma pap_Tcount_le_boundary_of_coherentSelector_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : pap_CoherentSelector ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.pap_Tcount_le_boundary_of_coherentSelector ω n hn h

/--
[pap_burton_keane_bernoulli_of_coherentSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PrivateArmProve.lean)
-/
@[path]
private lemma pap_burton_keane_bernoulli_of_coherentSelector_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → pap_CoherentSelector ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.pap_burton_keane_bernoulli_of_coherentSelector hd p hp1 hp0 hres htrif


-- created on 2026-10-23
