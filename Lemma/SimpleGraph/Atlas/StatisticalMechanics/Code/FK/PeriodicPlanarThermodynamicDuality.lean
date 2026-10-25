import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarThermodynamicDuality.Part2
open MeasureTheory Filter Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[dualConfigEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarThermodynamicDuality.lean)
-/
@[path]
private lemma dualConfigEquiv_apply_eq
  {edgeDual : E ≃ F}
  {omega : ConfigSpace E}
  {f : F} :
-- imply
  dualConfigEquiv edgeDual omega f = !(omega (edgeDual.symm f)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.dualConfigEquiv_apply edgeDual omega f

/--
[dualConfigEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarThermodynamicDuality.lean)
-/
@[path]
private lemma dualConfigEquiv_symm_apply_eq
  {edgeDual : E ≃ F}
  {eta : ConfigSpace F}
  {e : E} :
-- imply
  (dualConfigEquiv edgeDual).symm eta e = !(eta (edgeDual e)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.dualConfigEquiv_symm_apply edgeDual eta e

/--
[continuous_dualConfigEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarThermodynamicDuality.lean)
-/
@[path]
private lemma continuous_dualConfigEquiv_eq
  {edgeDual : E ≃ F} :
-- imply
  Continuous (dualConfigEquiv edgeDual) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.continuous_dualConfigEquiv edgeDual

/--
[continuous_dualConfigEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarThermodynamicDuality.lean)
-/
@[path]
private lemma continuous_dualConfigEquiv_symm_eq
  {edgeDual : E ≃ F} :
-- imply
  Continuous (dualConfigEquiv edgeDual).symm := by
-- proof
  apply StatMech.FK.PeriodicPlanar.continuous_dualConfigEquiv_symm edgeDual

/--
[dualConfigEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarThermodynamicDuality.lean)
-/
@[path]
private lemma dualConfigEquiv_symm_eq
  {edgeDual : E ≃ F} :
-- imply
  dualConfigEquiv edgeDual.symm = (dualConfigEquiv edgeDual).symm := by
-- proof
  apply StatMech.FK.PeriodicPlanar.dualConfigEquiv_symm edgeDual

/--
[weakLimit_dual_of_finite_exchange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarThermodynamicDuality.lean)
-/
@[path]
private lemma weakLimit_dual_of_finite_exchange_eq
  [Countable E]
  [Countable F]
  {edgeDual : E ≃ F}
  {mu : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {muDual : ℕ → ProbabilityMeasure (ConfigSpace F)}
  {nu : ProbabilityMeasure (ConfigSpace E)}
  {nuDual : ProbabilityMeasure (ConfigSpace F)}
-- given
  (hfinite : ∀ n, muDual n = (mu n).map (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable)
  (hmu : WeakConvergesTo mu nu)
  (hdual : WeakConvergesTo muDual nuDual) :
-- imply
  nuDual = nu.map (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable := by
-- proof
  apply StatMech.FK.PeriodicPlanar.weakLimit_dual_of_finite_exchange edgeDual mu muDual nu nuDual hfinite hmu hdual

/--
[weakLimit_dual_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarThermodynamicDuality.lean)
-/
@[path]
private lemma weakLimit_dual_event_eq
  [Countable E]
  [Countable F]
  {edgeDual : E ≃ F}
  {nu : ProbabilityMeasure (ConfigSpace E)}
  {nuDual : ProbabilityMeasure (ConfigSpace F)}
  {A : Set (ConfigSpace F)}
-- given
  (hdual : nuDual = nu.map (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable)
  (hA : MeasurableSet A) :
-- imply
  (nuDual : Measure (ConfigSpace F)) A = (nu : Measure (ConfigSpace E)) ((dualConfigEquiv edgeDual) ⁻¹' A) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.weakLimit_dual_event edgeDual nu nuDual hdual hA

/--
[weakLimit_dual_of_subsequence_exchange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarThermodynamicDuality.lean)
-/
@[path]
private lemma weakLimit_dual_of_subsequence_exchange_eq
  [Countable E]
  [Countable F]
  {edgeDual : E ≃ F}
  {mu : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {muDual : ℕ → ProbabilityMeasure (ConfigSpace F)}
  {phi : ℕ → ℕ}
  {nu : ProbabilityMeasure (ConfigSpace E)}
  {nuDual : ProbabilityMeasure (ConfigSpace F)}
-- given
  (hfinite : ∀ n, muDual n = (mu n).map (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable)
  (hmu : WeakConvergesTo (fun n => mu (phi n)) nu)
  (hdual : WeakConvergesTo (fun n => muDual (phi n)) nuDual) :
-- imply
  nuDual = nu.map (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable := by
-- proof
  apply StatMech.FK.PeriodicPlanar.weakLimit_dual_of_subsequence_exchange edgeDual mu muDual phi nu nuDual hfinite hmu hdual

/--
[exists_common_weak_dual_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarThermodynamicDuality.lean)
-/
@[path]
private lemma exists_common_weak_dual_limits_eq
  [Countable E]
  [Countable F]
  {edgeDual : E ≃ F}
  {mu : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {muDual : ℕ → ProbabilityMeasure (ConfigSpace F)}
-- given
  (hfinite : ∀ n, muDual n = (mu n).map (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable) :
-- imply
  ∃ (phi : ℕ → ℕ) (nu : ProbabilityMeasure (ConfigSpace E)) (nuDual : ProbabilityMeasure (ConfigSpace F)), StrictMono phi ∧ WeakConvergesTo (fun n => mu (phi n)) nu ∧ WeakConvergesTo (fun n => muDual (phi n)) nuDual ∧ nuDual = nu.map (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_common_weak_dual_limits edgeDual mu muDual hfinite

/--
[PeriodicGraph.free_wired_bufferedInfiniteVolume_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarThermodynamicDuality.lean)
-/
@[path]
private lemma free_wired_bufferedInfiniteVolume_dual_eq
  [Countable E]
  [Countable F]
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {Pdual : PeriodicGraph W}
  {edgeDual : Sym2 V ≃ Sym2 W}
  {p pDual q qDual : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hpDual : 0 < pDual)
  (hpDual1 : pDual < 1)
  (hqDual : 1 ≤ qDual)
  (hfinite : ∀ n, Pdual.wiredBufferedMeasure n hpDual hpDual1 (zero_lt_one.trans_le hqDual) = (P.freeBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq)).map (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable) :
-- imply
  Pdual.wiredBufferedInfiniteVolume hpDual hpDual1 (zero_lt_one.trans_le hqDual) = (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)).map (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.free_wired_bufferedInfiniteVolume_dual P Pdual edgeDual hp hp1 hq hpDual hpDual1 hqDual hfinite

/--
[PeriodicGraph.wired_free_bufferedInfiniteVolume_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarThermodynamicDuality.lean)
-/
@[path]
private lemma wired_free_bufferedInfiniteVolume_dual_eq
  [Countable E]
  [Countable F]
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {Pdual : PeriodicGraph W}
  {edgeDual : Sym2 V ≃ Sym2 W}
  {p pDual q qDual : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hpDual : 0 < pDual)
  (hpDual1 : pDual < 1)
  (hqDual : 1 ≤ qDual)
  (hfinite : ∀ n, Pdual.freeBufferedMeasure n hpDual hpDual1 (zero_lt_one.trans_le hqDual) = (P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq)).map (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable) :
-- imply
  Pdual.freeBufferedInfiniteVolume hpDual hpDual1 (zero_lt_one.trans_le hqDual) = (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)).map (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wired_free_bufferedInfiniteVolume_dual P Pdual edgeDual hp hp1 hq hpDual hpDual1 hqDual hfinite


-- created on 2026-10-23
