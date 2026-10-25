import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc33witness.Part3
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc33_split_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_split_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Sharpness.Current V} :
-- imply
  Fintype.card {K : Sharpness.Current V // ∀ e, K e ≤ m e} = ∏ e : Sym2 V, (m e + 1) := by
-- proof
  apply StatMech.Walls.gc33_split_card G m

/--
[gc33_split_term_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_split_term_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Sharpness.Current V}
  {K : Sharpness.Current V}
-- given
  (h01 : ∀ e ∈ G.edgeFinset, m e ≤ 1)
  (hK : ∀ e, K e ≤ m e) :
-- imply
  Sharpness.weight G β J K * Sharpness.weight G β J (fun e => m e - K e) = Sharpness.weight G β J m := by
-- proof
  apply StatMech.Walls.gc33_split_term_eq G β J m h01 K hK

/--
[gc33_mass_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_mass_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Sharpness.Current V}
  {S : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (h01 : ∀ e ∈ G.edgeFinset, m e ≤ 1) :
-- imply
  hnw_mass G β J m S ≤ (Fintype.card {K : Sharpness.Current V // ∀ e, K e ≤ m e} : ℝ) * Sharpness.weight G β J m := by
-- proof
  apply StatMech.Walls.gc33_mass_le G β J hβ hJ m h01 S

/--
[gc33_connP_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_connP_isolated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {P : Finset (Sym2 V)}
  {a : V}
  {b : V}
-- given
  (ha : ∀ e ∈ P, a ∉ e)
  (h : connP P a b) :
-- imply
  a = b := by
-- proof
  apply StatMech.Walls.gc33_connP_isolated G ha h

/--
[gc33_J_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_J_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∀ e, 0 ≤ gc33_J e := by
-- proof
  apply StatMech.Walls.gc33_J_nonneg G

/--
[gc33_ma_01](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_ma_01_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∀ e ∈ gc33_G.edgeFinset, gc33_ma e ≤ 1 := by
-- proof
  apply StatMech.Walls.gc33_ma_01 G

/--
[gc33_ma_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_ma_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Sharpness.sources gc33_G gc33_ma = (∅ : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc33_ma_sources G

/--
[gc33_mstar_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_mstar_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Sharpness.sources gc33_G gc33_mstar = (∅ : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc33_mstar_sources G

/--
[gc33_ma_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_ma_conn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : Fin 5}
-- given
  (hab : a ≠ b)
  (he : gc33_ma s(a, b) = 1) :
-- imply
  connP (oddEdges gc33_G.edgeFinset gc33_ma) a b := by
-- proof
  apply StatMech.Walls.gc33_ma_conn G a b hab he

/--
[gc33_ma_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_ma_allConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  hnw_allConn gc33_G gc33_ma 0 1 2 := by
-- proof
  apply StatMech.Walls.gc33_ma_allConn G

/--
[gc33_mstar_posEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_mstar_posEdges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  posEdges gc33_G.edgeFinset gc33_mstar = {s(3, 4)} := by
-- proof
  apply StatMech.Walls.gc33_mstar_posEdges G

/--
[gc33_mstar_noneConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_mstar_noneConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  hnw_noneConn gc33_G gc33_mstar 0 1 2 := by
-- proof
  apply StatMech.Walls.gc33_mstar_noneConn G

/--
[gc33_weight_ma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_weight_ma_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Sharpness.weight gc33_G 1 gc33_J gc33_ma = 1 := by
-- proof
  apply StatMech.Walls.gc33_weight_ma G

/--
[gc33_weight_mstar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_weight_mstar_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Sharpness.weight gc33_G 1 gc33_J gc33_mstar = 32 := by
-- proof
  apply StatMech.Walls.gc33_weight_mstar G

/--
[gc33_mass_ma_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_mass_ma_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  hnw_mass gc33_G 1 gc33_J gc33_ma ∅ ≤ 8 := by
-- proof
  apply StatMech.Walls.gc33_mass_ma_le G

/--
[gc33_mass_ma_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_mass_ma_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  0 < hnw_mass gc33_G 1 gc33_J gc33_ma ∅ := by
-- proof
  apply StatMech.Walls.gc33_mass_ma_pos G

/--
[gc33_mass_mstar_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_mass_mstar_ge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  32 ≤ hnw_mass gc33_G 1 gc33_J gc33_mstar ∅ := by
-- proof
  apply StatMech.Walls.gc33_mass_mstar_ge G

/--
[gc33_doubling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_doubling_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  2 * hnw_mass gc33_G 1 gc33_J gc33_ma ∅ ≤ hnw_mass gc33_G 1 gc33_J gc33_mstar ∅ := by
-- proof
  apply StatMech.Walls.gc33_doubling G

/--
[gc33_ma_ne_mstar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_ma_ne_mstar_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  gc33_ma ≠ gc33_mstar := by
-- proof
  apply StatMech.Walls.gc33_ma_ne_mstar G

/--
[gc33_allFilter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_allFilter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  bbr_allFilter gc33_G gc33_M 0 1 2 = {gc33_ma} := by
-- proof
  apply StatMech.Walls.gc33_allFilter G

/--
[gc33_mstar_in_noneFilter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_mstar_in_noneFilter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  gc33_mstar ∈ bbr_noneFilter gc33_G gc33_M 0 1 2 := by
-- proof
  apply StatMech.Walls.gc33_mstar_in_noneFilter G

/--
[gc33_massDoubling_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_massDoubling_witness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  gc31_MassDoublingSurgery gc33_G 1 gc33_J gc33_M ∅ 0 1 2 := by
-- proof
  apply StatMech.Walls.gc33_massDoubling_witness G

/--
[gc33_backboneSurgery_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_backboneSurgery_witness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  bbr_BackboneSurgery gc33_G 1 gc33_J gc33_M ∅ 0 1 2 := by
-- proof
  apply StatMech.Walls.gc33_backboneSurgery_witness G

/--
[gc33_witness_positive_masses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_witness_positive_masses_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  0 < hnw_mass gc33_G 1 gc33_J gc33_ma ∅ ∧ 0 < hnw_mass gc33_G 1 gc33_J gc33_mstar ∅ ∧ 0 < 2 * hnw_mass gc33_G 1 gc33_J gc33_ma ∅ ∧ 2 * hnw_mass gc33_G 1 gc33_J gc33_ma ∅ ≤ hnw_mass gc33_G 1 gc33_J gc33_mstar ∅ := by
-- proof
  apply StatMech.Walls.gc33_witness_positive_masses G

/--
[gc33_massDoubling_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_massDoubling_of_injection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Sharpness.Current V)}
  {B : Finset V}
  {o x y : V}
  {Φ : Sharpness.Current V → Sharpness.Current V}
-- given
  (hmem : ∀ m ∈ bbr_allFilter G M o x y, Φ m ∈ bbr_noneFilter G M o x y)
  (hinj : Set.InjOn Φ (bbr_allFilter G M o x y))
  (hdoub : ∀ m ∈ bbr_allFilter G M o x y, 2 * hnw_mass G β J m B ≤ hnw_mass G β J (Φ m) B) :
-- imply
  gc31_MassDoublingSurgery G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc33_massDoubling_of_injection G G β J M B o x y Φ hmem hinj hdoub

/--
[gc33_surgery_unsat_of_zero_targets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_surgery_unsat_of_zero_targets_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Sharpness.Current V)}
  {B : Finset V}
  {o x y : V}
  {ma : Sharpness.Current V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hma : ma ∈ bbr_allFilter G M o x y)
  (hpos : 0 < hnw_mass G β J ma B)
  (hzero : ∀ m' ∈ bbr_noneFilter G M o x y, hnw_mass G β J m' B = 0) :
-- imply
  ¬ gc31_MassDoublingSurgery G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc33_surgery_unsat_of_zero_targets G G β J hβ hJ M B o x y ma hma hpos hzero

/--
[gc33_mass_summand_cut_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_mass_summand_cut_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m K : Sharpness.Current V}
  [DecidablePred p]
-- given
  (p : Sym2 V → Prop) :
-- imply
  Sharpness.weight G β J K * Sharpness.weight G β J (fun e => m e - K e) = (Sharpness.weight G β J (StatMech.Ising.restrictCut K p) * Sharpness.weight G β J (StatMech.Ising.restrictCut (fun e => m e - K e) p)) * (Sharpness.weight G β J (StatMech.Ising.restrictCut K (fun e => ¬ p e)) * Sharpness.weight G β J (StatMech.Ising.restrictCut (fun e => m e - K e) (fun e => ¬ p e))) := by
-- proof
  apply StatMech.Walls.gc33_mass_summand_cut_factor G G β J m K p

/--
[gc33_massDoubling_of_sourceClusterResummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_massDoubling_of_sourceClusterResummation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Sharpness.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (h : gc33_SourceClusterResummation G β J M B o x y) :
-- imply
  gc31_MassDoublingSurgery G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc33_massDoubling_of_sourceClusterResummation G G β J hβ hJ M B o x y h

/--
[gc33_B_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean)
-/
@[path]
private lemma gc33_B_status_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Sharpness.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  (gc33_SourceClusterResummation G β J M B o x y → gc31_MassDoublingSurgery G β J M B o x y) ∧ (∀ (ma : Sharpness.Current V), ma ∈ bbr_allFilter G M o x y → 0 < hnw_mass G β J ma B → (∀ m' ∈ bbr_noneFilter G M o x y, hnw_mass G β J m' B = 0) → ¬ gc31_MassDoublingSurgery G β J M B o x y) := by
-- proof
  apply StatMech.Walls.gc33_B_status G G β J hβ hJ M B o x y


-- created on 2026-10-23
