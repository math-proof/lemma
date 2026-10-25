import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.TwoFoldForestArmsClose.Part3
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[tffa_count_unsat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldForestArmsClose.lean)
-/
@[path]
private lemma tffa_count_unsat_eq
  {d : ℕ}
  {f : Option (Fin 4 × Fin 2) → Fin 6}
-- given
  (hf : Function.Injective f) :
-- imply
  False := by
-- proof
  apply StatMech.Percolation.tffa_count_unsat f hf

/--
[tffa_not_twoFoldForestArms_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldForestArmsClose.lean)
-/
@[path]
private lemma tffa_not_twoFoldForestArms_of_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hclaw : tffa_TwoFoldClawConfig ω n) :
-- imply
  ¬ tfh_TwoFoldForestArms ω n := by
-- proof
  apply StatMech.Percolation.tffa_not_twoFoldForestArms_of_claw ω n hclaw

/--
[tffa_claw_excludes_twoFoldForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldForestArmsClose.lean)
-/
@[path]
private lemma tffa_claw_excludes_twoFoldForestArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hclaw : tffa_TwoFoldClawConfig ω n)
  (h : tfh_TwoFoldForestArms ω n) :
-- imply
  False := by
-- proof
  apply StatMech.Percolation.tffa_claw_excludes_twoFoldForestArms ω n hclaw h

/--
[tffa_claw_coloring_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldForestArmsClose.lean)
-/
@[path]
private lemma tffa_claw_coloring_consistent_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {_n : ℕ}
  {rep : Fin 6 → Site d}
-- given
  (hcover : ∀ u, (cluster d (removeSites T ω) u).Infinite → ∃ i, Connected d (removeSites T ω) (rep i) u) :
-- imply
  ∃ κ : Site d → Fin 6, ∀ u v, (cluster d (removeSites T ω) u).Infinite → (cluster d (removeSites T ω) v).Infinite → κ u = κ v → aed_sameGlobalComponent T ω u v := by
-- proof
  apply StatMech.Percolation.tffa_claw_coloring_consistent T ω _n rep hcover

/--
[tffa_twoFoldClawConfig_of_sixArmCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldForestArmsClose.lean)
-/
@[path]
private lemma tffa_twoFoldClawConfig_of_sixArmCover_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ : Site d}
  {y : Fin 3 → Site d}
  {rep : Fin 6 → Site d}
-- given
  (hx0 : x₀ ∈ box d n ∧ IsTrifurcation d ω x₀)
  (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i)
  (hyinj : Function.Injective y)
  (hexhaust : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
  (hcover : ∀ u, (cluster d (removeSites (tfc_trifFinset ω n) ω) u).Infinite → ∃ i, Connected d (removeSites (tfc_trifFinset ω n) ω) (rep i) u) :
-- imply
  tffa_TwoFoldClawConfig ω n := by
-- proof
  apply StatMech.Percolation.tffa_twoFoldClawConfig_of_sixArmCover ω n hx0 hydata hyinj hexhaust rep hcover

/--
[tffa_spanningTreeLeafCount_of_leafDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldForestArmsClose.lean)
-/
@[path]
private lemma tffa_spanningTreeLeafCount_of_leafDisjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : tffa_LeafDisjointSelection ω n)
  (hbase : (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
-- imply
  flc2_SpanningTreeLeafCount ω n := by
-- proof
  apply StatMech.Percolation.tffa_spanningTreeLeafCount_of_leafDisjoint ω n h hbase

/--
[tffa_leafDisjoint_of_twoFoldForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldForestArmsClose.lean)
-/
@[path]
private lemma tffa_leafDisjoint_of_twoFoldForestArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : tfh_TwoFoldForestArms ω n) :
-- imply
  tffa_LeafDisjointSelection ω n := by
-- proof
  apply StatMech.Percolation.tffa_leafDisjoint_of_twoFoldForestArms ω n hn h


-- created on 2026-10-23
