import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.baoallopen.Part2
open Set SimpleGraph Finset MeasureTheory StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Walls


/--
[bao_allOpenTrif_imp_bc67](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baoallopen.lean)
-/
@[path]
private lemma bao_allOpenTrif_imp_bc67_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
-- given
  (h : bao_AllOpenTrif ω L) :
-- imply
  bc67_IsGnTrifurcation ω L (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bao_allOpenTrif_imp_bc67 h

/--
[bao_box_internallyConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baoallopen.lean)
-/
@[path]
private lemma bao_box_internallyConnected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {x y : Site 2}
-- given
  (h : bao_AllOpenTrif ω L)
  (hx : x ∈ Lattice.box 2 L)
  (hy : y ∈ Lattice.box 2 L) :
-- imply
  Lattice.Connected 2 ω x y := by
-- proof
  apply StatMech.Walls.bao_box_internallyConnected h hx hy

/--
[bao_boxEdges_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baoallopen.lean)
-/
@[path]
private lemma bao_boxEdges_fst_eq
  {n : ℕ}
  {x y : Site 2}
-- given
  (h : s(x, y) ∈ boxEdges 2 n) :
-- imply
  x ∈ Lattice.box 2 n := by
-- proof
  apply StatMech.Walls.bao_boxEdges_fst h

/--
[bao_onlyBox0_allOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baoallopen.lean)
-/
@[path]
private lemma bao_onlyBox0_allOpen_eq
  {L : ℕ} :
-- imply
  bff_BoxAllOpen (bao_onlyBox0 L) L := by
-- proof
  apply StatMech.Walls.bao_onlyBox0_allOpen L

/--
[bao_bgn_idx_box10](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baoallopen.lean)
-/
@[path]
private lemma bao_bgn_idx_box10_eq
  {L : ℕ}
-- given
  (hL : 1 ≤ L)
  (h : ℤ)
  (hh0 : 0 ≤ h)
  (hhL : h ≤ (L : ℤ)) :
-- imply
  bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) h) = bc57_pt 1 0 := by
-- proof
  apply StatMech.Walls.bao_bgn_idx_box10 hL h hh0 hhL

/--
[bao_bgn_idx_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baoallopen.lean)
-/
@[path]
private lemma bao_bgn_idx_zero_eq
  {L : ℕ} :
-- imply
  bgn_idx L (0 : Site 2) = 0 := by
-- proof
  apply StatMech.Walls.bao_bgn_idx_zero L

/--
[bao_u_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baoallopen.lean)
-/
@[path]
private lemma bao_u_isolated_eq
  {L : ℕ}
  {w : Site 2}
-- given
  (hL : 1 ≤ L) :
-- imply
  ¬ (openSubgraph 2 (removeSites (bc61_boxAround 2 L 0) (bao_onlyBox0 L))).Adj (bc57_pt (2 * (L : ℤ) + 1) 0) w := by
-- proof
  apply StatMech.Walls.bao_u_isolated hL w

/--
[bao_cut_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baoallopen.lean)
-/
@[path]
private lemma bao_cut_singleton_eq
  {L : ℕ}
  {z : Site 2}
-- given
  (hL : 1 ≤ L)
  (h : Connected 2 (removeSites (bc61_boxAround 2 L 0) (bao_onlyBox0 L)) (bc57_pt (2 * (L : ℤ) + 1) 0) z) :
-- imply
  z = bc57_pt (2 * (L : ℤ) + 1) 0 := by
-- proof
  apply StatMech.Walls.bao_cut_singleton hL h

/--
[bao_allOpen_not_frees_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baoallopen.lean)
-/
@[path]
private lemma bao_allOpen_not_frees_bridge_eq
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  bff_BoxAllOpen (bao_onlyBox0 L) L ∧ ¬ bsc_BoxesInternallyConnected (bao_onlyBox0 L) L (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bao_allOpen_not_frees_bridge hL

/--
[bao_bk_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baoallopen.lean)
-/
@[path]
private lemma bao_bk_of_forest_eq
-- given
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bao_bk_of_forest p hp1 hp0 hdata

/--
[bao_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baoallopen.lean)
-/
@[path]
private lemma bao_status_eq
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))), bao_AllOpenTrif ω L → bc67_IsGnTrifurcation ω L (0 : Site 2)) ∧ (bff_BoxAllOpen (bao_onlyBox0 L) L ∧ ¬ bsc_BoxesInternallyConnected (bao_onlyBox0 L) L (0 : Site 2)) ∧ (∀ (p : NNReal) (hp1 : p ≤ 1), 0 < p → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
-- proof
  apply StatMech.Walls.bao_status hL


-- created on 2026-10-23
