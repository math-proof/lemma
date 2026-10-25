import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.DecoupledForestCount.Part4
open StatMech StatMech.Percolation


/--
[dfc_Tcount_le_boundary_succ_of_boxOpenForestSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DecoupledForestCount.lean)
-/
@[path]
private lemma dfc_Tcount_le_boundary_succ_of_boxOpenForestSucc_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : dfc_BoxOpenForestSucc ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d (n + 1) := by
-- proof
  apply StatMech.Percolation.dfc_Tcount_le_boundary_succ_of_boxOpenForestSucc ω n h

/--
[dfc_spanForestArmsSucc_of_armForestReaching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DecoupledForestCount.lean)
-/
@[path]
private lemma dfc_spanForestArmsSucc_of_armForestReaching_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : dfc_ArmForestReachingSucc ω n) :
-- imply
  dfc_SpanForestArmsSucc ω n := by
-- proof
  apply StatMech.Percolation.dfc_spanForestArmsSucc_of_armForestReaching ω n h

/--
[dfc_boxOpenForestSucc_of_spanForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DecoupledForestCount.lean)
-/
@[path]
private lemma dfc_boxOpenForestSucc_of_spanForestArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : dfc_SpanForestArmsSucc ω n) :
-- imply
  dfc_BoxOpenForestSucc ω n := by
-- proof
  apply StatMech.Percolation.dfc_boxOpenForestSucc_of_spanForestArms ω n h

/--
[dfc_armForestReachingSucc_of_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DecoupledForestCount.lean)
-/
@[path]
private lemma dfc_armForestReachingSucc_of_canonical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
  (hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) :
-- imply
  dfc_ArmForestReachingSucc ω n := by
-- proof
  apply StatMech.Percolation.dfc_armForestReachingSucc_of_canonical ω n hn hcanon hexists

/--
[dfc_Tcount_le_boundary_succ_of_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DecoupledForestCount.lean)
-/
@[path]
private lemma dfc_Tcount_le_boundary_succ_of_canonical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d (n + 1) := by
-- proof
  apply StatMech.Percolation.dfc_Tcount_le_boundary_succ_of_canonical ω n hn hcanon

/--
[dfc_canonTcount_le_boundary_succ_of_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DecoupledForestCount.lean)
-/
@[path]
private lemma dfc_canonTcount_le_boundary_succ_of_canonical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x) :
-- imply
  ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d (n + 1) := by
-- proof
  apply StatMech.Percolation.dfc_canonTcount_le_boundary_succ_of_canonical ω n hn hcanon

/--
[dfc_canonTcount_le_boundary_succ_of_canonBoxOpenForestSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DecoupledForestCount.lean)
-/
@[path]
private lemma dfc_canonTcount_le_boundary_succ_of_canonBoxOpenForestSucc_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : dfc_CanonBoxOpenForestSucc ω n) :
-- imply
  ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d (n + 1) := by
-- proof
  apply StatMech.Percolation.dfc_canonTcount_le_boundary_succ_of_canonBoxOpenForestSucc ω n h

/--
[dfc_canonSpanForestArmsSucc_of_armForestReaching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DecoupledForestCount.lean)
-/
@[path]
private lemma dfc_canonSpanForestArmsSucc_of_armForestReaching_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : dfc_CanonArmForestReachingSucc ω n) :
-- imply
  dfc_CanonSpanForestArmsSucc ω n := by
-- proof
  apply StatMech.Percolation.dfc_canonSpanForestArmsSucc_of_armForestReaching ω n h

/--
[dfc_canonBoxOpenForestSucc_of_spanForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DecoupledForestCount.lean)
-/
@[path]
private lemma dfc_canonBoxOpenForestSucc_of_spanForestArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : dfc_CanonSpanForestArmsSucc ω n) :
-- imply
  dfc_CanonBoxOpenForestSucc ω n := by
-- proof
  apply StatMech.Percolation.dfc_canonBoxOpenForestSucc_of_spanForestArms ω n h

/--
[dfc_canonArmForestReachingSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DecoupledForestCount.lean)
-/
@[path]
private lemma dfc_canonArmForestReachingSucc_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hexists : ∃ x, x ∈ box d n ∧ IsCanonicalTrifurcation d ω x) :
-- imply
  dfc_CanonArmForestReachingSucc ω n := by
-- proof
  apply StatMech.Percolation.dfc_canonArmForestReachingSucc ω n hn hexists

/--
[dfc_canonTcount_le_boundary_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DecoupledForestCount.lean)
-/
@[path]
private lemma dfc_canonTcount_le_boundary_succ_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d (n + 1) := by
-- proof
  apply StatMech.Percolation.dfc_canonTcount_le_boundary_succ ω n hn


-- created on 2026-10-23
