import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PlacementClose.Part2
open MeasureTheory Filter Topology SimpleGraph Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[plc_relift_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean)
-/
@[path]
private lemma plc_relift_image_eq
  {d : ℕ}
  {N₀ N : ℕ}
  {t₀ : Finset (Sym2 (boxVerts d N₀))}
-- given
  (h : N₀ ≤ N) :
-- imply
  (t₀.image (innerEdgeLE d h)).image (edgeIncl d N) = t₀.image (edgeIncl d N₀) := by
-- proof
  apply StatMech.FK.plc_relift_image N₀ N h t₀

/--
[plc_common_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean)
-/
@[path]
private lemma plc_common_box_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {s : Finset (Sym2 (Site d))} :
-- imply
  ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))), s = t.image (edgeIncl d N) ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N) := by
-- proof
  apply StatMech.FK.plc_common_box g s

/--
[plc_htrans_iff_centred_shift_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean)
-/
@[path]
private lemma plc_htrans_iff_centred_shift_wired_eq
  {d : ℕ}
  {m : ℕ}
  {v : Site d}
  {N : ℕ}
  {t t' : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hNm : N ≤ m) :
-- imply
  (med_multiMassProb (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2) ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v))) = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) (t'.image (innerEdgeLE d hNm))) ↔ (med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) (t.image (innerEdgeLE d hNm)) = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) (t'.image (innerEdgeLE d hNm))) := by
-- proof
  apply StatMech.FK.plc_htrans_iff_centred_shift_wired m v N hNm t t'

/--
[plc_htrans_iff_centred_shift_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean)
-/
@[path]
private lemma plc_htrans_iff_centred_shift_free_eq
  {d : ℕ}
  {m : ℕ}
  {v : Site d}
  {N : ℕ}
  {t t' : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hNm : N ≤ m) :
-- imply
  (med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p 2) ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v))) = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm))) ↔ (med_multiMassProb (fkProb (boxGraph d m) p 2) (t.image (innerEdgeLE d hNm)) = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm))) := by
-- proof
  apply StatMech.FK.plc_htrans_iff_centred_shift_free m v N hNm t t'

/--
[plc_wiredPlacement_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean)
-/
@[path]
private lemma plc_wiredPlacement_of_decay_eq
  {d : ℕ}
  {p : ℝ}
  {g : Multiplicative (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdecay : ∀ s : Finset (Sym2 (Site d)), ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))), s = t.image (edgeIncl d N) ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N) ∧ plc_WiredCentredShiftDecay hp hp1 N t t') :
-- imply
  med_wiredPlacement hp hp1 g := by
-- proof
  apply StatMech.FK.plc_wiredPlacement_of_decay hp hp1 g hdecay

/--
[plc_freePlacement_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean)
-/
@[path]
private lemma plc_freePlacement_of_decay_eq
  {d : ℕ}
  {p : ℝ}
  {g : Multiplicative (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdecay : ∀ s : Finset (Sym2 (Site d)), ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))), s = t.image (edgeIncl d N) ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N) ∧ plc_FreeCentredShiftDecay hp hp1 N t t') :
-- imply
  med_freePlacement hp hp1 g := by
-- proof
  apply StatMech.FK.plc_freePlacement_of_decay hp hp1 g hdecay

/--
[plc_wiredCentredShiftDecay_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean)
-/
@[path]
private lemma plc_wiredCentredShiftDecay_refl_eq
  {d : ℕ}
  {p : ℝ}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  plc_WiredCentredShiftDecay hp hp1 N t t := by
-- proof
  apply StatMech.FK.plc_wiredCentredShiftDecay_refl hp hp1 N t

/--
[plc_freeCentredShiftDecay_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean)
-/
@[path]
private lemma plc_freeCentredShiftDecay_refl_eq
  {d : ℕ}
  {p : ℝ}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  plc_FreeCentredShiftDecay hp hp1 N t t := by
-- proof
  apply StatMech.FK.plc_freeCentredShiftDecay_refl hp hp1 N t

/--
[plc_wiredCentredShiftDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean)
-/
@[path]
private lemma plc_wiredCentredShiftDecay_one_eq
  {d : ℕ}
  {p : ℝ}
  {s : Finset (Sym2 (Site d))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))), s = t.image (edgeIncl d N) ∧ s.image (fun e => (1 : Multiplicative (Site d))⁻¹ • e) = t'.image (edgeIncl d N) ∧ plc_WiredCentredShiftDecay hp hp1 N t t' := by
-- proof
  apply StatMech.FK.plc_wiredCentredShiftDecay_one hp hp1 s

/--
[plc_freeCentredShiftDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean)
-/
@[path]
private lemma plc_freeCentredShiftDecay_one_eq
  {d : ℕ}
  {p : ℝ}
  {s : Finset (Sym2 (Site d))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))), s = t.image (edgeIncl d N) ∧ s.image (fun e => (1 : Multiplicative (Site d))⁻¹ • e) = t'.image (edgeIncl d N) ∧ plc_FreeCentredShiftDecay hp hp1 N t t' := by
-- proof
  apply StatMech.FK.plc_freeCentredShiftDecay_one hp hp1 s

/--
[plc_wiredPlacement_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean)
-/
@[path]
private lemma plc_wiredPlacement_one_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  med_wiredPlacement hp hp1 (1 : Multiplicative (Site d)) := by
-- proof
  apply StatMech.FK.plc_wiredPlacement_one hp hp1

/--
[plc_freePlacement_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean)
-/
@[path]
private lemma plc_freePlacement_one_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  med_freePlacement hp hp1 (1 : Multiplicative (Site d)) := by
-- proof
  apply StatMech.FK.plc_freePlacement_one hp hp1

/--
[plc_wiredIV_isTranslationInvariant_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean)
-/
@[path]
private lemma plc_wiredIV_isTranslationInvariant_of_decay_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdecay : ∀ (g : Multiplicative (Site d)) (s : Finset (Sym2 (Site d))), ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))), s = t.image (edgeIncl d N) ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N) ∧ plc_WiredCentredShiftDecay hp hp1 N t t') :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.plc_wiredIV_isTranslationInvariant_of_decay hp hp1 hdecay

/--
[plc_freeIV_isTranslationInvariant_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean)
-/
@[path]
private lemma plc_freeIV_isTranslationInvariant_of_decay_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdecay : ∀ (g : Multiplicative (Site d)) (s : Finset (Sym2 (Site d))), ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))), s = t.image (edgeIncl d N) ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N) ∧ plc_FreeCentredShiftDecay hp hp1 N t t') :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.plc_freeIV_isTranslationInvariant_of_decay hp hp1 hdecay


-- created on 2026-10-23
