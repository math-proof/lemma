import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.OffCentreCarrier
open MeasureTheory Filter Topology SimpleGraph Set StatMech StatMech.FK


/--
[occ_translated_eq_centred_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreCarrier.lean)
-/
@[path]
private lemma occ_translated_eq_centred_wired_eq
  {d : ℕ}
  {N : ℕ}
  {v : Site d}
  {eb' : Sym2 (boxVerts d N)}
  {p q : ℝ}
  {k : ℕ} :
-- imply
  edgeMargProb (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p q) (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb')) = edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p q) (innerEdgeLE d (Nat.le_add_right N k) eb') := by
-- proof
  apply StatMech.FK.occ_translated_eq_centred_wired N v eb' k

/--
[occ_translated_tendsto_wiredDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreCarrier.lean)
-/
@[path]
private lemma occ_translated_tendsto_wiredDensity_eq
  {d : ℕ}
  {N : ℕ}
  {v : Site d}
  {eb' : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun k => edgeMargProb (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p 2) (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb'))) atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb') p)) := by
-- proof
  apply StatMech.FK.occ_translated_tendsto_wiredDensity N v eb' hp hp1

/--
[occ_translated_between_iv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreCarrier.lean)
-/
@[path]
private lemma occ_translated_between_iv_eq
  {d : ℕ}
  {N : ℕ}
  {v : Site d}
  {eb' : Sym2 (boxVerts d N)}
  {p : ℝ}
  {k : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N eb') p ≤ edgeMargProb (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p 2) (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb')) := by
-- proof
  apply StatMech.FK.occ_translated_between_iv N v eb' hp hp1 k

/--
[occ_free_eq_wired_at_continuity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreCarrier.lean)
-/
@[path]
private lemma occ_free_eq_wired_at_continuity_eq
  {d : ℕ}
  {N : ℕ}
  {eb' : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p → wiredEdgeDensity d 2 (edgeIncl d N eb') p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb') p)
  (hpmem : p ∈ Ioo (0:ℝ) 1)
  (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb')) (Ioo (0:ℝ) 1) p) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N eb') p = wiredEdgeDensity d 2 (edgeIncl d N eb') p := by
-- proof
  apply StatMech.FK.occ_free_eq_wired_at_continuity N eb' hsecant hpmem hcont

/--
[occ_free_eq_wired_off_countable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreCarrier.lean)
-/
@[path]
private lemma occ_free_eq_wired_off_countable_eq
  {d : ℕ}
  {N : ℕ}
  {eb' : Sym2 (boxVerts d N)}
-- given
  (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p → wiredEdgeDensity d 2 (edgeIncl d N eb') p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb') p) :
-- imply
  ∃ S : Set ℝ, S.Countable ∧ ∀ p ∈ Ioo (0:ℝ) 1, p ∉ S → freeEdgeDensity d 2 (edgeIncl d N eb') p = wiredEdgeDensity d 2 (edgeIncl d N eb') p := by
-- proof
  apply StatMech.FK.occ_free_eq_wired_off_countable N eb' hsecant

/--
[occ_offCentreCarrier_squeeze](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreCarrier.lean)
-/
@[path]
private lemma occ_offCentreCarrier_squeeze_eq
  {d : ℕ}
  {N : ℕ}
  {v : Site d}
  {eb' : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fbd_offCentreCarrier N v eb' p 2) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.occ_offCentreCarrier_squeeze N v eb' hp hp1

/--
[occ_offCentreCarrier_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreCarrier.lean)
-/
@[path]
private lemma occ_offCentreCarrier_eq_zero_eq
  {d : ℕ}
  {N : ℕ}
  {v : Site d}
  {eb' : Sym2 (boxVerts d N)}
  {p q : ℝ}
  {k : ℕ} :
-- imply
  fbd_offCentreCarrier N v eb' p q k = 0 := by
-- proof
  apply StatMech.FK.occ_offCentreCarrier_eq_zero N v eb' p q k

/--
[occ_offCentreCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreCarrier.lean)
-/
@[path]
private lemma occ_offCentreCarrier_eq
  {d : ℕ}
  {N : ℕ}
  {v : Site d}
  {eb' : Sym2 (boxVerts d N)}
  {p : ℝ} :
-- imply
  Tendsto (fbd_offCentreCarrier N v eb' p 2) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.occ_offCentreCarrier N v eb' p

/--
[occ_wired_density_eq_of_translation_cofinal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreCarrier.lean)
-/
@[path]
private lemma occ_wired_density_eq_of_translation_cofinal_eq
  {d : ℕ}
  {N : ℕ}
  {v : Site d}
  {eb eb' : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (htrans : ∀ k, edgeMargProb (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p 2) (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb')) = edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb)) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb') p := by
-- proof
  apply StatMech.FK.occ_wired_density_eq_of_translation_cofinal N v eb eb' hp hp1 htrans


-- created on 2026-10-23
