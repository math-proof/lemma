import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.SecantClose
open MeasureTheory Set Filter Topology Real StatMech StatMech.FK


/--
[fsc_logistic_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean)
-/
@[path]
private lemma fsc_logistic_pos_eq
  {t : ℝ} :
-- imply
  0 < fsc_logistic t := by
-- proof
  apply StatMech.FK.fsc_logistic_pos t

/--
[fsc_logistic_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean)
-/
@[path]
private lemma fsc_logistic_lt_one_eq
  {t : ℝ} :
-- imply
  fsc_logistic t < 1 := by
-- proof
  apply StatMech.FK.fsc_logistic_lt_one t

/--
[fsc_logistic_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean)
-/
@[path]
private lemma fsc_logistic_mem_Ioo_eq
  {t : ℝ} :
-- imply
  fsc_logistic t ∈ Ioo (0 : ℝ) 1 := by
-- proof
  apply StatMech.FK.fsc_logistic_mem_Ioo t

/--
[fsc_logistic_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean)
-/
@[path]
private lemma fsc_logistic_strictMono_eq :
-- imply
  StrictMono fsc_logistic := by
-- proof
  apply StatMech.FK.fsc_logistic_strictMono

/--
[fsc_logistic_logit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean)
-/
@[path]
private lemma fsc_logistic_logit_eq
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  fsc_logistic (fsc_logit p) = p := by
-- proof
  apply StatMech.FK.fsc_logistic_logit hp hp1

/--
[fsc_secant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean)
-/
@[path]
private lemma fsc_secant_eq
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hdata : fsc_FreeEnergyData d N eb) :
-- imply
  ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p → wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p := by
-- proof
  apply StatMech.FK.fsc_secant d N eb hdata

/--
[fsc_softplus_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean)
-/
@[path]
private lemma fsc_softplus_hasDerivAt_eq
  {t : ℝ} :
-- imply
  HasDerivAt fsc_softplus (fsc_logistic t) t := by
-- proof
  apply StatMech.FK.fsc_softplus_hasDerivAt t

/--
[fsc_deriv_softplus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean)
-/
@[path]
private lemma fsc_deriv_softplus_eq :
-- imply
  deriv fsc_softplus = fsc_logistic := by
-- proof
  apply StatMech.FK.fsc_deriv_softplus

/--
[fsc_softplus_differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean)
-/
@[path]
private lemma fsc_softplus_differentiable_eq :
-- imply
  Differentiable ℝ fsc_softplus := by
-- proof
  apply StatMech.FK.fsc_softplus_differentiable

/--
[fsc_softplus_convexOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean)
-/
@[path]
private lemma fsc_softplus_convexOn_eq :
-- imply
  ConvexOn ℝ univ fsc_softplus := by
-- proof
  apply StatMech.FK.fsc_softplus_convexOn

/--
[fsc_softplus_pressureRightDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean)
-/
@[path]
private lemma fsc_softplus_pressureRightDeriv_eq
  {t : ℝ} :
-- imply
  pressureRightDeriv fsc_softplus t = fsc_logistic t := by
-- proof
  apply StatMech.FK.fsc_softplus_pressureRightDeriv t

/--
[fsc_softplus_pressureLeftDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean)
-/
@[path]
private lemma fsc_softplus_pressureLeftDeriv_eq
  {t : ℝ} :
-- imply
  pressureLeftDeriv fsc_softplus t = fsc_logistic t := by
-- proof
  apply StatMech.FK.fsc_softplus_pressureLeftDeriv t

/--
[fsc_freeEnergyData_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean)
-/
@[path]
private lemma fsc_freeEnergyData_satisfiable_eq :
-- imply
  ∃ g : ℝ → ℝ, ConvexOn ℝ univ g ∧ (∀ t, fsc_logistic t = pressureRightDeriv g t) ∧ (∀ t, fsc_logistic t = pressureLeftDeriv g t) := by
-- proof
  apply StatMech.FK.fsc_freeEnergyData_satisfiable

/--
[fk_uniqueness_q2_secant_from_freeEnergyData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean)
-/
@[path]
private lemma fk_uniqueness_q2_secant_from_freeEnergyData_eq
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hdata : fsc_FreeEnergyData d N eb) :
-- imply
  ∃ S : Set ℝ, S.Countable ∧ ∀ p ∉ S, ∀ (hp : 0 < p) (hp1 : p < 1) (phi : Measure (ConfigSpace (Sym2 (Site d)))), ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ≤ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))) → phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
-- proof
  apply StatMech.FK.fk_uniqueness_q2_secant_from_freeEnergyData d N eb hdata


-- created on 2026-10-23
