import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalCountFinal
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[ccf_armsRemoveSiteInfinite_of_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalCountFinal.lean)
-/
@[path]
private lemma ccf_armsRemoveSiteInfinite_of_canonical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x) :
-- imply
  arc_TrifArmsRemoveSiteInfinite ω n := by
-- proof
  apply StatMech.Percolation.ccf_armsRemoveSiteInfinite_of_canonical ω n hcanon

/--
[ccf_canon_arm_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalCountFinal.lean)
-/
@[path]
private lemma ccf_canon_arm_data_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
-- given
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x) :
-- imply
  ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d), (∀ i, (openSubgraph d ω).Adj x (c i)) ∧ (∀ i, c i ≠ x) ∧ (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧ ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧ ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧ (∀ i, zr i ∈ vertexBoundary d (n + 1) ∧ ∃ w : (openSubgraph d (removeSite x ω)).Walk (c i) (zr i), x ∉ w.support) := by
-- proof
  apply StatMech.Percolation.ccf_canon_arm_data ω n hcanon x hxbox htri

/--
[ccf_canon_count_of_armForestReaching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalCountFinal.lean)
-/
@[path]
private lemma ccf_canon_count_of_armForestReaching_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : sfa_ArmForestReaching ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.ccf_canon_count_of_armForestReaching ω n h

/--
[ccf_canon_count_of_boxOpenForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalCountFinal.lean)
-/
@[path]
private lemma ccf_canon_count_of_boxOpenForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bst_BoxOpenForest ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.ccf_canon_count_of_boxOpenForest ω n h

/--
[ccf_canon_count_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalCountFinal.lean)
-/
@[path]
private lemma ccf_canon_count_single_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
  {c : Fin 3 → Site d}
-- given
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x)
  (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
  (hadj : ∀ i, (openSubgraph d ω).Adj x (c i))
  (hne : ∀ i, c i ≠ x)
  (hcut : ¬ Connected d (removeSite x ω) (c 0) (c 1) ∧ ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧ ¬ Connected d (removeSite x ω) (c 1) (c 2))
  (hbdry : ∀ i, c i ∈ vertexBoundary d n)
  (hinj : Function.Injective c) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.ccf_canon_count_single ω n hxbox htri hsingle c hadj hne hcut hbdry hinj

/--
[ccf_canon_count_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalCountFinal.lean)
-/
@[path]
private lemma ccf_canon_count_subsingleton_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n → IsTrifurcation d ω y → x = y) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.ccf_canon_count_subsingleton ω n hn hsub

/--
[ccf_canonTcount_le_boundary_of_armForestReaching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalCountFinal.lean)
-/
@[path]
private lemma ccf_canonTcount_le_boundary_of_armForestReaching_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : sfa_ArmForestReaching ω n) :
-- imply
  ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.ccf_canonTcount_le_boundary_of_armForestReaching ω n h

/--
[ccf_canonTcount_le_boundary_of_boxOpenForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalCountFinal.lean)
-/
@[path]
private lemma ccf_canonTcount_le_boundary_of_boxOpenForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bst_BoxOpenForest ω n) :
-- imply
  ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.ccf_canonTcount_le_boundary_of_boxOpenForest ω n h

/--
[ccf_canonTcount_le_boundary_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalCountFinal.lean)
-/
@[path]
private lemma ccf_canonTcount_le_boundary_subsingleton_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n → IsTrifurcation d ω y → x = y) :
-- imply
  ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.ccf_canonTcount_le_boundary_subsingleton ω n hn hsub

/--
[ccf_truthcheck_canon_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalCountFinal.lean)
-/
@[path]
private lemma ccf_truthcheck_canon_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
  {c : Fin 3 → Site d}
-- given
  (hxbox : x ∈ box d n)
  (htri : IsCanonicalTrifurcation d ω x)
  (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
  (hadj : ∀ i, (openSubgraph d ω).Adj x (c i))
  (hne : ∀ i, c i ≠ x)
  (hcut : ¬ Connected d (removeSite x ω) (c 0) (c 1) ∧ ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧ ¬ Connected d (removeSite x ω) (c 1) (c 2))
  (hbdry : ∀ i, c i ∈ vertexBoundary d n)
  (hinj : Function.Injective c) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.ccf_truthcheck_canon_claw ω n hxbox htri hsingle c hadj hne hcut hbdry hinj


-- created on 2026-10-23
