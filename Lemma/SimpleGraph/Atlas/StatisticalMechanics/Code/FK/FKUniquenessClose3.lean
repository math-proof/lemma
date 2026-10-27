import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose3
open MeasureTheory Set Filter Topology StatMech StatMech.FK


/--
[freeEdgeDensity_q2_le_wiredEdgeDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose3.lean)
-/
@[path]
private lemma freeEdgeDensity_q2_le_wiredEdgeDensity_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N eb) p ≤ wiredEdgeDensity d 2 (edgeIncl d N eb) p := by
-- proof
  apply StatMech.FK.freeEdgeDensity_q2_le_wiredEdgeDensity d N eb hp hp1

/--
[density_le_of_secant_continuousWithinAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose3.lean)
-/
@[path]
private lemma density_le_of_secant_continuousWithinAt_eq
  {d : ℕ}
  {b : ℝ → ℝ}
  {a p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hcont : ContinuousWithinAt b (Ioo (0:ℝ) 1) p)
  (hsec : ∀ p' ∈ Ioo (0:ℝ) 1, p' < p → b p' ≤ a) :
-- imply
  b p ≤ a := by
-- proof
  apply StatMech.FK.density_le_of_secant_continuousWithinAt hp0 hp1 hcont hsec

/--
[heq_at_cont_q2_of_secant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose3.lean)
-/
@[path]
private lemma heq_at_cont_q2_of_secant_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p → wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p) :
-- imply
  ∀ p ∈ Ioo (0 : ℝ) 1, ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p → freeEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb) p := by
-- proof
  apply StatMech.FK.heq_at_cont_q2_of_secant d N eb hsecant

/--
[fk_uniqueness_off_countable_q2_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose3.lean)
-/
@[path]
private lemma fk_uniqueness_off_countable_q2_full_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p → wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p) :
-- imply
  ∃ S : Set ℝ, S.Countable ∧ ∀ p ∉ S, ∀ (hp : 0 < p) (hp1 : p < 1) (phi : Measure (ConfigSpace (Sym2 (Site d)))), ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ≤ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))) → phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
-- proof
  apply StatMech.FK.fk_uniqueness_off_countable_q2_full d N eb hsecant


-- created on 2026-10-23
