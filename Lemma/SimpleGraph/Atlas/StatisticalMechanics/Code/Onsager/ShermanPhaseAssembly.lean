import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ShermanPhaseAssembly.Part5
open StatMech StatMech.Onsager


/--
[ons_KWmatPhase_loopSum_two_bucket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_KWmatPhase_loopSum_two_bucket_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  {x omega : ℂ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I) :
-- imply
  (∑ d : Fin (n + 1) → ons_Dart L, ons_loopWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) d) = 2 * ons_phaseBucketE L x omega a b e n + ons_phaseBucketN L x omega a b e n := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_loopSum_two_bucket x omega homega a b e

/--
[ons_KWmatPhase_mask_loopSum_two_bucket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_KWmatPhase_mask_loopSum_two_bucket_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  {x omega : ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  (∑ d : Fin (n + 1) → ons_Dart L, ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b))) d) = 2 * ons_maskPhaseBucketE L x omega a b forbidden e n + ons_maskPhaseBucketN L x omega a b forbidden e n := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_mask_loopSum_two_bucket x omega homega a b forbidden hforbidden e

/--
[ons_KWmatPhase_det_eq_two_bucket_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_KWmatPhase_det_eq_two_bucket_exp_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x omega : ℂ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hspec : ∀ alpha ∈ (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots, ‖alpha‖ < 1) :
-- imply
  (1 - ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)).det = Complex.exp (-∑' n : ℕ, (2 * ons_phaseBucketE L x omega a b e n + ons_phaseBucketN L x omega a b e n) / ((n : ℂ) + 1)) := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_det_eq_two_bucket_exp x omega homega a b e hspec

/--
[ons_KWmatPhase_det_eq_A_mul_bucket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_KWmatPhase_det_eq_A_mul_bucket_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x omega : ℂ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hspec : ∀ alpha ∈ (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots, ‖alpha‖ < 1)
  (hB : Summable (fun n : ℕ => ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)))
  (hN : Summable (fun n : ℕ => ons_phaseBucketN L x omega a b e n / ((n : ℂ) + 1))) :
-- imply
  (1 - ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)).det = Complex.exp (-∑' n : ℕ, ons_phaseBucketN L x omega a b e n / ((n : ℂ) + 1)) * Complex.exp (-2 * ∑' n : ℕ, ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_det_eq_A_mul_bucket x omega homega a b e hspec hB hN

/--
[ons_phaseBucketSeries_eq_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_phaseBucketSeries_eq_geometric_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x omega : ℂ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (hsum : Summable fun s => ‖ons_firstReturnWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) e (ons_dartRev L e) s‖)
  (hsmall : ∑' s, ‖ons_firstReturnWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) e (ons_dartRev L e) s‖ < 1) :
-- imply
  (∑' n : ℕ, ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) = ∑' k : ℕ, (∑' s, ons_firstReturnWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) e (ons_dartRev L e) s) ^ (k + 1) / (k + 1) := by
-- proof
  apply StatMech.Onsager.ons_phaseBucketSeries_eq_geometric x omega a b e hsum hsmall

/--
[ons_summable_phaseBucketE_firstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_summable_phaseBucketE_firstReturn_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x omega : ℂ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (hsum : Summable fun s => ‖ons_firstReturnWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) e (ons_dartRev L e) s‖)
  (hsmall : ∑' s, ‖ons_firstReturnWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) e (ons_dartRev L e) s‖ < 1) :
-- imply
  Summable fun n : ℕ => ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1) := by
-- proof
  apply StatMech.Onsager.ons_summable_phaseBucketE_firstReturn x omega a b e hsum hsmall

/--
[ons_hlam_spinPhase_firstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_hlam_spinPhase_firstReturn_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x omega : ℂ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (hsum : Summable fun s => ‖ons_firstReturnWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) e (ons_dartRev L e) s‖)
  (hsmall : ∑' s, ‖ons_firstReturnWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) e (ons_dartRev L e) s‖ < 1) :
-- imply
  Complex.exp (-∑' n : ℕ, ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) = 1 - ∑' s, ons_firstReturnWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) e (ons_dartRev L e) s := by
-- proof
  apply StatMech.Onsager.ons_hlam_spinPhase_firstReturn x omega a b e hsum hsmall

/--
[ons_KWmatPhase_spectral_Sherman_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_KWmatPhase_spectral_Sherman_small_eq
  {L : ℕ}
  [NeZero L]
  {x : ℝ}
  {a b : Fin 2}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
-- imply
  ∀ alpha ∈ (ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots, ‖alpha‖ < 1 := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_spectral_Sherman_small L hx a b

/--
[ons_spinWalkRoot_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_spinWalkRoot_sq_eq
  {L : ℕ}
  [NeZero L]
  {x : ℝ}
  {a b : Fin 2}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
-- imply
  ons_spinWalkRoot L x a b ^ 2 = (1 - ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).det := by
-- proof
  apply StatMech.Onsager.ons_spinWalkRoot_sq L hx a b

/--
[ons_phaseAvoidRoot_eq_maskRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_phaseAvoidRoot_eq_maskRoot_eq
  {L : ℕ}
  [NeZero L]
  {x : ℝ}
  {a b : Fin 2}
  {e : ons_Dart L} :
-- imply
  ons_phaseAvoidRoot L x a b e = ons_detWalkRoot (ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L)) (ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) := by
-- proof
  apply StatMech.Onsager.ons_phaseAvoidRoot_eq_maskRoot L x a b e

/--
[ons_spinWalkRoot_factor_firstReturn_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_spinWalkRoot_factor_firstReturn_small_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x : ℝ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
-- imply
  ons_spinWalkRoot L x a b = ons_phaseAvoidRoot L x a b e * (1 - ∑' s, ons_firstReturnWeight (ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) e (ons_dartRev L e) s) := by
-- proof
  apply StatMech.Onsager.ons_spinWalkRoot_factor_firstReturn_small L hx a b e

/--
[ons_summable_phaseBucketN_Sherman_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_summable_phaseBucketN_Sherman_small_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x : ℝ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
-- imply
  Summable fun n : ℕ => ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n / ((n : ℂ) + 1) := by
-- proof
  apply StatMech.Onsager.ons_summable_phaseBucketN_Sherman_small L hx a b e

/--
[ons_detWalkRoot_mask_delete_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_detWalkRoot_mask_delete_pair_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x : ℝ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  ons_detWalkRoot (ons_maskMatrix forbidden (ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) = ons_detWalkRoot (ons_maskMatrix (({e, ons_dartRev L e} : Finset (ons_Dart L)) ∪ forbidden) (ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) * (1 - ∑' s, ons_firstReturnWeight (ons_maskMatrix forbidden (ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) e (ons_dartRev L e) s) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_mask_delete_pair L hx a b forbidden hforbidden e

/--
[ons_addDartPair_rev_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_addDartPair_rev_closed_eq
  {L : ℕ}
  {forbidden : Finset (ons_Dart L)}
  {e d : ons_Dart L}
-- given
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  ons_dartRev L d ∈ ons_addDartPair L forbidden e ↔ d ∈ ons_addDartPair L forbidden e := by
-- proof
  apply StatMech.Onsager.ons_addDartPair_rev_closed L forbidden hforbidden e d

/--
[ons_subset_maskAfter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_subset_maskAfter_eq
  {L : ℕ}
  {forbidden : Finset (ons_Dart L)}
  {es : List (ons_Dart L)} :
-- imply
  forbidden ⊆ ons_maskAfter L forbidden es := by
-- proof
  apply StatMech.Onsager.ons_subset_maskAfter L forbidden es

/--
[ons_mem_maskAfter_of_mem_list](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_mem_maskAfter_of_mem_list_eq
  {L : ℕ}
  {forbidden : Finset (ons_Dart L)}
  {es : List (ons_Dart L)}
  {d : ons_Dart L}
-- given
  (hd : d ∈ es) :
-- imply
  d ∈ ons_maskAfter L forbidden es := by
-- proof
  apply StatMech.Onsager.ons_mem_maskAfter_of_mem_list L forbidden es hd

/--
[ons_detWalkRoot_mask_eliminate_list](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_detWalkRoot_mask_eliminate_list_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x : ℝ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {es : List (ons_Dart L)}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  ons_detWalkRoot (ons_maskMatrix forbidden (ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) = ons_detWalkRoot (ons_maskMatrix (ons_maskAfter L forbidden es) (ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) * ons_maskEliminationProduct L x a b forbidden es := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_mask_eliminate_list L hx a b forbidden hforbidden es

/--
[ons_spinWalkRoot_eq_eliminationProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_spinWalkRoot_eq_eliminationProduct_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x : ℝ}
  {a b : Fin 2}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
-- imply
  ons_spinWalkRoot L x a b = ons_maskEliminationProduct L x a b ∅ (Finset.univ : Finset (ons_Dart L)).toList := by
-- proof
  apply StatMech.Onsager.ons_spinWalkRoot_eq_eliminationProduct L hx a b

/--
[ons_KWmatPhase_det_eq_A_mul_firstReturn_sq_Sherman_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean)
-/
@[path]
private lemma ons_KWmatPhase_det_eq_A_mul_firstReturn_sq_Sherman_small_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x : ℝ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
-- imply
  (1 - ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).det = Complex.exp (-∑' n : ℕ, ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n / ((n : ℂ) + 1)) * (1 - ∑' s, ons_firstReturnWeight (ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) e (ons_dartRev L e) s) ^ 2 := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_det_eq_A_mul_firstReturn_sq_Sherman_small L hx a b e


-- created on 2026-10-23
