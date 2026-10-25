import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLoops
open StatMech StatMech.Onsager


/--
[ons_loopWeight_KWmatPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_loopWeight_KWmatPhase_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {x omega u v : ℂ}
  {d : Fin n → ons_Dart L} :
-- imply
  ons_loopWeight (ons_KWmatPhase L x omega u v) d = (∏ k, ons_dirPhase u v (d k).2) * ons_loopWeight (ons_KWmat L x omega) d := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_KWmatPhase x omega u v d

/--
[ons_loopWeight_KWmatPhase_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_loopWeight_KWmatPhase_zpow_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {x omega u v : ℂ}
  {d : Fin n → ons_Dart L}
-- given
  (hu : u ≠ 0)
  (hv : v ≠ 0) :
-- imply
  ons_loopWeight (ons_KWmatPhase L x omega u v) d = u ^ (∑ k, ons_dirExponentX (d k).2) * v ^ (∑ k, ons_dirExponentY (d k).2) * ons_loopWeight (ons_KWmat L x omega) d := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_KWmatPhase_zpow x omega u v hu hv d

/--
[ons_dirExponentX_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_dirExponentX_step_eq
  {L : ℕ}
  {mu : Fin 4}
  {p : ZMod L × ZMod L} :
-- imply
  (((ons_dirExponentX mu : ℤ) : ZMod L)) = (ons_dirStep L mu p).1 - p.1 := by
-- proof
  apply StatMech.Onsager.ons_dirExponentX_step L mu p

/--
[ons_dirExponentY_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_dirExponentY_step_eq
  {L : ℕ}
  {mu : Fin 4}
  {p : ZMod L × ZMod L} :
-- imply
  (((ons_dirExponentY mu : ℤ) : ZMod L)) = (ons_dirStep L mu p).2 - p.2 := by
-- proof
  apply StatMech.Onsager.ons_dirExponentY_step L mu p

/--
[ons_sum_dirExponentX_cast_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_sum_dirExponentX_cast_zero_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  (((∑ k, ons_dirExponentX (d k).2 : ℤ) : ZMod L)) = 0 := by
-- proof
  apply StatMech.Onsager.ons_sum_dirExponentX_cast_zero d hvalid

/--
[ons_sum_dirExponentY_cast_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_sum_dirExponentY_cast_zero_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  (((∑ k, ons_dirExponentY (d k).2 : ℤ) : ZMod L)) = 0 := by
-- proof
  apply StatMech.Onsager.ons_sum_dirExponentY_cast_zero d hvalid

/--
[ons_loop_winding_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_loop_winding_exists_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  ∃ mx my : ℤ, (∑ k, ons_dirExponentX (d k).2) = (L : ℤ) * mx ∧ (∑ k, ons_dirExponentY (d k).2) = (L : ℤ) * my := by
-- proof
  apply StatMech.Onsager.ons_loop_winding_exists d hvalid

/--
[ons_loopWeight_spinPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_loopWeight_spinPhase_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {x omega : ℂ}
  {a b : Fin 2}
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  ∃ mx my : ℤ, (∑ k, ons_dirExponentX (d k).2) = (L : ℤ) * mx ∧ (∑ k, ons_dirExponentY (d k).2) = (L : ℤ) * my ∧ ons_loopWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) d = (-1 : ℂ) ^ ((a.val : ℤ) * mx + (b.val : ℤ) * my) * ons_loopWeight (ons_KWmat L x omega) d := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_spinPhase x omega a b d hvalid

/--
[ons_dirExponentX_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_dirExponentX_opposite_eq
  {mu : Fin 4} :
-- imply
  ons_dirExponentX (mu + 2) = -ons_dirExponentX mu := by
-- proof
  apply StatMech.Onsager.ons_dirExponentX_opposite mu

/--
[ons_dirExponentY_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_dirExponentY_opposite_eq
  {mu : Fin 4} :
-- imply
  ons_dirExponentY (mu + 2) = -ons_dirExponentY mu := by
-- proof
  apply StatMech.Onsager.ons_dirExponentY_opposite mu

/--
[ons_loopRev_sum_dirExponentX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_loopRev_sum_dirExponentX_eq
  {L n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L} :
-- imply
  ∑ k, ons_dirExponentX ((ons_loopRev L d k).2) = -∑ k, ons_dirExponentX ((d k).2) := by
-- proof
  apply StatMech.Onsager.ons_loopRev_sum_dirExponentX d

/--
[ons_loopRev_sum_dirExponentY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_loopRev_sum_dirExponentY_eq
  {L n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L} :
-- imply
  ∑ k, ons_dirExponentY ((ons_loopRev L d k).2) = -∑ k, ons_dirExponentY ((d k).2) := by
-- proof
  apply StatMech.Onsager.ons_loopRev_sum_dirExponentY d

/--
[ons_loopWeight_spinPhase_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_loopWeight_spinPhase_loopRev_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {x omega : ℂ}
  {a b : Fin 2}
  {d : Fin n → ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I) :
-- imply
  ons_loopWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) (ons_loopRev L d) = ons_loopWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) d := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_spinPhase_loopRev x omega homega a b d

/--
[ons_loopRev_hits_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_loopRev_hits_iff_eq
  {L n : ℕ}
  [NeZero n]
  {forbidden : Finset (ons_Dart L)}
  {d : Fin n → ons_Dart L}
-- given
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  (∃ k, ons_loopRev L d k ∈ forbidden) ↔ ∃ k, d k ∈ forbidden := by
-- proof
  apply StatMech.Onsager.ons_loopRev_hits_iff forbidden hforbidden d

/--
[ons_loopWeight_spinPhase_mask_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_loopWeight_spinPhase_mask_loopRev_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {x omega : ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {d : Fin n → ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b))) (ons_loopRev L d) = ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b))) d := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_spinPhase_mask_loopRev x omega homega a b forbidden hforbidden d

/--
[ons_loopSum_spinPhase_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_loopSum_spinPhase_symm_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {x omega : ℂ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I) :
-- imply
  (∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L => (∃ i, d i = e) ∧ ¬ ∃ j, d j = ons_dartRev L e)), ons_loopWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) d) = ∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L => (∃ i, d i = ons_dartRev L e) ∧ ¬ ∃ j, d j = e)), ons_loopWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) d := by
-- proof
  apply StatMech.Onsager.ons_loopSum_spinPhase_symm x omega homega a b e

/--
[ons_loopSum_spinPhase_mask_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_loopSum_spinPhase_mask_symm_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {x omega : ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  (∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L => (∃ i, d i = e) ∧ ¬ ∃ j, d j = ons_dartRev L e)), ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b))) d) = ∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L => (∃ i, d i = ons_dartRev L e) ∧ ¬ ∃ j, d j = e)), ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b))) d := by
-- proof
  apply StatMech.Onsager.ons_loopSum_spinPhase_mask_symm x omega homega a b forbidden hforbidden e

/--
[norm_ons_KWmatPhase_spin_entry_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma norm_ons_KWmatPhase_spin_entry_le_eq
  {L : ℕ}
  {x : ℝ}
  {a b : Fin 2}
  {d2 d1 : ons_Dart L} :
-- imply
  ‖ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d2 d1‖ ≤ ‖(x : ℂ)‖ := by
-- proof
  apply StatMech.Onsager.norm_ons_KWmatPhase_spin_entry_le L x a b d2 d1

/--
[ons_KWmatPhase_firstReturnWeight_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_KWmatPhase_firstReturnWeight_small_eq
  {L : ℕ}
  [NeZero L]
  {x : ℝ}
  {a b : Fin 2}
  {e r : ons_Dart L}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
-- imply
  Summable (fun s => ‖ons_firstReturnWeight (ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) e r s‖) ∧ (∑' s, ‖ons_firstReturnWeight (ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) e r s‖) < 1 := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_firstReturnWeight_small L hx a b e r

/--
[ons_KWmatPhase_filteredLoopSeries_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLoops.lean)
-/
@[path]
private lemma ons_KWmatPhase_filteredLoopSeries_summable_eq
  {L : ℕ}
  [NeZero L]
  {x : ℝ}
  {a b : Fin 2}
  [∀ n, DecidablePred (P n)]
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
  (P : (n : ℕ) → (Fin (n + 1) → ons_Dart L) → Prop) :
-- imply
  Summable fun n : ℕ => (∑ d ∈ Finset.univ.filter (P n), ons_loopWeight (ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) d) / ((n : ℂ) + 1) := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_filteredLoopSeries_summable L hx a b P


-- created on 2026-10-23
