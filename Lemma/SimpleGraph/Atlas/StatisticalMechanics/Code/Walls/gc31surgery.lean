import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc31surgery.Part3
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc31_flux_monotone_not_noneConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean)
-/
@[path]
private lemma gc31_flux_monotone_not_noneConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {Ψ : Sharpness.Current V → Sharpness.Current V}
  {m : Sharpness.Current V}
  {o x y : V}
-- given
  (hmono : ∀ e, m e ≤ Ψ m e)
  (hall : hnw_allConn G m o x y) :
-- imply
  ¬ hnw_noneConn G (Ψ m) o x y := by
-- proof
  apply StatMech.Walls.gc31_flux_monotone_not_noneConn G Ψ m hmono hall

/--
[gc31_addBackbone_not_noneConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean)
-/
@[path]
private lemma gc31_addBackbone_not_noneConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Sharpness.Current V}
  {P : Finset (Sym2 V)}
  {o x y : V}
-- given
  (hall : hnw_allConn G m o x y) :
-- imply
  ¬ hnw_noneConn G (hmu_addBackbone P m) o x y := by
-- proof
  apply StatMech.Walls.gc31_addBackbone_not_noneConn G m P hall

/--
[gc31_backboneSurgery_of_massDoubling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean)
-/
@[path]
private lemma gc31_backboneSurgery_of_massDoubling_eq
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
  (h : gc31_MassDoublingSurgery G β J M B o x y) :
-- imply
  bbr_BackboneSurgery G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc31_backboneSurgery_of_massDoubling G β J M B o x y h

/--
[gc31_native_gap_nonneg_of_massDoubling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean)
-/
@[path]
private lemma gc31_native_gap_nonneg_of_massDoubling_eq
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
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = B)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
  (h : gc31_MassDoublingSurgery G β J M B o x y) :
-- imply
  0 ≤ ∑ m ∈ M, hnw_gap G β J m B o x y := by
-- proof
  apply StatMech.Walls.gc31_native_gap_nonneg_of_massDoubling G β J hβ hJ M hnd B hm hox hoy hxy hcoh h

/--
[gc31_massDoubling_of_singleton_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean)
-/
@[path]
private lemma gc31_massDoubling_of_singleton_dominated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Sharpness.Current V)}
  {B : Finset V}
  {o x y : V}
  {ma mstar : Sharpness.Current V}
-- given
  (hsingle : bbr_allFilter G M o x y = {ma})
  (hstar : mstar ∈ bbr_noneFilter G M o x y)
  (hdom : 2 * hnw_mass G β J ma B ≤ hnw_mass G β J mstar B) :
-- imply
  gc31_MassDoublingSurgery G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc31_massDoubling_of_singleton_dominated G β J M B o x y ma mstar hsingle hstar hdom

/--
[gc31_mass_zero_of_odd_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean)
-/
@[path]
private lemma gc31_mass_zero_of_odd_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Sharpness.Current V}
  {S : Finset V}
-- given
  (hodd : ¬ Even S.card) :
-- imply
  hnw_mass G β J m S = 0 := by
-- proof
  apply StatMech.Walls.gc31_mass_zero_of_odd_card G β J m S hodd

/--
[gc31_connP_empty_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean)
-/
@[path]
private lemma gc31_connP_empty_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : V}
-- given
  (h : connP (∅ : Finset (Sym2 V)) a b) :
-- imply
  a = b := by
-- proof
  apply StatMech.Walls.gc31_connP_empty_eq G h

/--
[gc31_zero_noneConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean)
-/
@[path]
private lemma gc31_zero_noneConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  hnw_noneConn hmu_TriG gc31_zeroM 0 1 2 := by
-- proof
  apply StatMech.Walls.gc31_zero_noneConn G

/--
[gc31_allFilter_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean)
-/
@[path]
private lemma gc31_allFilter_witness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  bbr_allFilter hmu_TriG ({hmu_triM, gc31_zeroM} : Finset (Sharpness.Current (Fin 3))) 0 1 2 = {hmu_triM} := by
-- proof
  apply StatMech.Walls.gc31_allFilter_witness G

/--
[gc31_zero_in_noneFilter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean)
-/
@[path]
private lemma gc31_zero_in_noneFilter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  gc31_zeroM ∈ bbr_noneFilter hmu_TriG ({hmu_triM, gc31_zeroM} : Finset (Sharpness.Current (Fin 3))) 0 1 2 := by
-- proof
  apply StatMech.Walls.gc31_zero_in_noneFilter G

/--
[gc31_massDoubling_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean)
-/
@[path]
private lemma gc31_massDoubling_witness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  gc31_MassDoublingSurgery hmu_TriG 1 (fun _ => 1) ({hmu_triM, gc31_zeroM} : Finset (Sharpness.Current (Fin 3))) ({0} : Finset (Fin 3)) 0 1 2 := by
-- proof
  apply StatMech.Walls.gc31_massDoubling_witness G

/--
[gc31_backboneSurgery_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean)
-/
@[path]
private lemma gc31_backboneSurgery_witness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  bbr_BackboneSurgery hmu_TriG 1 (fun _ => 1) ({hmu_triM, gc31_zeroM} : Finset (Sharpness.Current (Fin 3))) ({0} : Finset (Fin 3)) 0 1 2 := by
-- proof
  apply StatMech.Walls.gc31_backboneSurgery_witness G

/--
[gc31_massDoubling_fails_triangle_emptyB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean)
-/
@[path]
private lemma gc31_massDoubling_fails_triangle_emptyB_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ¬ gc31_MassDoublingSurgery hmu_TriG 1 (fun _ => 1) ({hmu_triM} : Finset (Sharpness.Current (Fin 3))) (∅ : Finset (Fin 3)) 0 1 2 := by
-- proof
  apply StatMech.Walls.gc31_massDoubling_fails_triangle_emptyB G


-- created on 2026-10-23
