import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.DecayOfCorrelations
open MeasureTheory Filter Topology SimpleGraph Set StatMech StatMech.FK


/--
[docGap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DecayOfCorrelations.lean)
-/
@[path]
private lemma docGap_nonneg_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  0 ≤ docGap d N eb p := by
-- proof
  apply StatMech.FK.docGap_nonneg d N eb hp hp1

/--
[docGap_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DecayOfCorrelations.lean)
-/
@[path]
private lemma docGap_tendsto_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb)) atTop (𝓝 (docGap d N eb p)) := by
-- proof
  apply StatMech.FK.docGap_tendsto d N eb hp hp1

/--
[doc_countable_density_discont](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DecayOfCorrelations.lean)
-/
@[path]
private lemma doc_countable_density_discont_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)} :
-- imply
  {p : ℝ | p ∈ Ioo (0:ℝ) 1 ∧ ¬ ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p}.Countable := by
-- proof
  apply StatMech.FK.doc_countable_density_discont d N eb

/--
[doc_gap_zero_at_continuity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DecayOfCorrelations.lean)
-/
@[path]
private lemma doc_gap_zero_at_continuity_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p → wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
  (hpmem : p ∈ Ioo (0:ℝ) 1)
  (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p) :
-- imply
  docGap d N eb p = 0 := by
-- proof
  apply StatMech.FK.doc_gap_zero_at_continuity d N eb hsecant hpmem hcont

/--
[doc_free_eq_wired_at_continuity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DecayOfCorrelations.lean)
-/
@[path]
private lemma doc_free_eq_wired_at_continuity_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p → wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
  (hpmem : p ∈ Ioo (0:ℝ) 1)
  (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb) p := by
-- proof
  apply StatMech.FK.doc_free_eq_wired_at_continuity d N eb hsecant hpmem hcont

/--
[doc_gap_zero_off_countable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DecayOfCorrelations.lean)
-/
@[path]
private lemma doc_gap_zero_off_countable_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p → wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p) :
-- imply
  ∃ S : Set ℝ, S.Countable ∧ ∀ p ∈ Ioo (0:ℝ) 1, p ∉ S → docGap d N eb p = 0 := by
-- proof
  apply StatMech.FK.doc_gap_zero_off_countable d N eb hsecant

/--
[doc_countable_gap_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DecayOfCorrelations.lean)
-/
@[path]
private lemma doc_countable_gap_pos_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p → wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p) :
-- imply
  {p : ℝ | p ∈ Ioo (0:ℝ) 1 ∧ docGap d N eb p ≠ 0}.Countable := by
-- proof
  apply StatMech.FK.doc_countable_gap_pos d N eb hsecant

/--
[doc_wired_free_interior_gap_decay_at_continuity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DecayOfCorrelations.lean)
-/
@[path]
private lemma doc_wired_free_interior_gap_decay_at_continuity_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p → wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
  (hpmem : p ∈ Ioo (0:ℝ) 1)
  (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p) :
-- imply
  Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb)) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.doc_wired_free_interior_gap_decay_at_continuity d N eb hsecant hpmem hcont

/--
[doc_decay_at_continuity_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DecayOfCorrelations.lean)
-/
@[path]
private lemma doc_decay_at_continuity_wired_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ} :
-- imply
  Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb))) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.doc_decay_at_continuity_wired S N eb

/--
[doc_decay_at_continuity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DecayOfCorrelations.lean)
-/
@[path]
private lemma doc_decay_at_continuity_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p → wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
  (hpmem : p ∈ Ioo (0:ℝ) 1)
  (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p) :
-- imply
  Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb))) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.doc_decay_at_continuity S N eb hsecant hpmem hcont

/--
[doc_translate_density_eq_at_continuity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DecayOfCorrelations.lean)
-/
@[path]
private lemma doc_translate_density_eq_at_continuity_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p → wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
  (hpmem : p ∈ Ioo (0:ℝ) 1)
  (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb) p ∧ wiredEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p ∧ freeEdgeDensity d 2 (edgeIncl d N eb) p = freeEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p := by
-- proof
  apply StatMech.FK.doc_translate_density_eq_at_continuity S N eb hsecant hpmem hcont

/--
[doc_gap_boxSym_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DecayOfCorrelations.lean)
-/
@[path]
private lemma doc_gap_boxSym_eq_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  docGap d N (Sym2.map (S.lift N) eb) p = docGap d N eb p := by
-- proof
  apply StatMech.FK.doc_gap_boxSym_eq S N eb hp hp1


-- created on 2026-10-23
