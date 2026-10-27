import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
open StatMech StatMech.Universality


/--
[isingLeapfrogStoppedKernel_eq_killed_add_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_eq_killed_add_exit_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedKernel R t p q = isingLeapfrogKilledKernel R t p q + isingLeapfrogExitKernel R t p q := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_eq_killed_add_exit R t p q

/--
[isingLeapfrogKilledKernel_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogKilledKernel_nonneg_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  0 ≤ isingLeapfrogKilledKernel R t p q := by
-- proof
  apply StatMech.Universality.isingLeapfrogKilledKernel_nonneg R t p q

/--
[isingLeapfrogExitKernel_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogExitKernel_nonneg_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  0 ≤ isingLeapfrogExitKernel R t p q := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernel_nonneg R t p q

/--
[isingLeapfrogExitKernel_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogExitKernel_le_one_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogExitKernel R t p q ≤ 1 := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernel_le_one R t p q

/--
[isingLeapfrogExitKernel_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogExitKernel_mono_eq
  {R : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  Monotone (fun t ↦ isingLeapfrogExitKernel R t p q) := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernel_mono R p q

/--
[isingLeapfrogExitKernel_tendsto_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogExitKernel_tendsto_limit_eq
  {R : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  Filter.Tendsto (fun t ↦ isingLeapfrogExitKernel R t p q) Filter.atTop (nhds (isingLeapfrogExitKernelLimit R p q)) := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernel_tendsto_limit R p q

/--
[isingLeapfrogExitKernel_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogExitKernel_succ_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogExitKernel R (t + 1) p q = if hp : isingLeapfrogBoxBoundary R p then isingLeapfrogExitKernel R t p q else (isingLeapfrogExitKernel R t (isingLeapfrogSW R p) q + isingLeapfrogExitKernel R t (isingLeapfrogSE R p hp) q + isingLeapfrogExitKernel R t (isingLeapfrogNW R p hp) q + isingLeapfrogExitKernel R t (isingLeapfrogNE R p hp) q) / 4 := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernel_succ R t p q

/--
[isingLeapfrogExitKernel_succ_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogExitKernel_succ_sub_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R}
-- given
  (hq : isingLeapfrogBoxBoundary R q) :
-- imply
  isingLeapfrogExitKernel R (t + 1) p q - isingLeapfrogExitKernel R t p q = ∑ r, isingLeapfrogKilledKernel R t p r * isingLeapfrogStoppedKernel R 1 r q := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernel_succ_sub R t p q hq

/--
[isingLeapfrogExitKernel_eq_sum_flux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogExitKernel_eq_sum_flux_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R}
-- given
  (hp : ¬ isingLeapfrogBoxBoundary R p)
  (hq : isingLeapfrogBoxBoundary R q) :
-- imply
  isingLeapfrogExitKernel R t p q = ∑ s ∈ range t, ∑ r, isingLeapfrogKilledKernel R s p r * isingLeapfrogStoppedKernel R 1 r q := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernel_eq_sum_flux R t p q hp hq

/--
[isingLeapfrogExitKernelLimit_meanValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogExitKernelLimit_meanValue_eq
  {R : Nat}
  {p q : IsingLeapfrogBox R}
-- given
  (hp : ¬ isingLeapfrogBoxBoundary R p) :
-- imply
  isingLeapfrogExitKernelLimit R (isingLeapfrogSW R p) q + isingLeapfrogExitKernelLimit R (isingLeapfrogSE R p hp) q + isingLeapfrogExitKernelLimit R (isingLeapfrogNW R p hp) q + isingLeapfrogExitKernelLimit R (isingLeapfrogNE R p hp) q = 4 * isingLeapfrogExitKernelLimit R p q := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernelLimit_meanValue R p q hp

/--
[isingLeapfrogExitKernel_sum_eq_boundaryMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogExitKernel_sum_eq_boundaryMass_eq
  {R t : Nat}
  {p : IsingLeapfrogBox R} :
-- imply
  ∑ q, isingLeapfrogExitKernel R t p q = isingLeapfrogStoppedBoundaryMass R t p := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernel_sum_eq_boundaryMass R t p

/--
[isingLeapfrogKilledKernel_sum_add_boundaryMass_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogKilledKernel_sum_add_boundaryMass_eq_one_eq
  {R t : Nat}
  {p : IsingLeapfrogBox R} :
-- imply
  (∑ q, isingLeapfrogKilledKernel R t p q) + isingLeapfrogStoppedBoundaryMass R t p = 1 := by
-- proof
  apply StatMech.Universality.isingLeapfrogKilledKernel_sum_add_boundaryMass_eq_one R t p

/--
[isingLeapfrogExitKernelTimeGradientSq_eq_sum_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogExitKernelTimeGradientSq_eq_sum_boundary_eq
  {R t t' : Nat}
  {p p' : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogExitKernelTimeGradientSq R t t' p p' = ∑ q with isingLeapfrogBoxBoundary R q, (isingLeapfrogStoppedKernel R t p q - isingLeapfrogStoppedKernel R t' p' q) ^ 2 := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernelTimeGradientSq_eq_sum_boundary R t t' p p'

/--
[isingLeapfrogStoppedKernelTimeGradientSq_le_killed_add_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernelTimeGradientSq_le_killed_add_exit_eq
  {R t t' : Nat}
  {p p' : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedKernelTimeGradientSq R t t' p p' ≤ 2 * (isingLeapfrogKilledKernelTimeGradientSq R t t' p p' + isingLeapfrogExitKernelTimeGradientSq R t t' p p') := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernelTimeGradientSq_le_killed_add_exit R t t' p p'

/--
[isingLeapfrogFreeKernel_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogFreeKernel_nonneg_eq
  {t : Nat}
  {p q : IsingLeapfrogPlane} :
-- imply
  0 ≤ isingLeapfrogFreeKernel t p q := by
-- proof
  apply StatMech.Universality.isingLeapfrogFreeKernel_nonneg t p q

/--
[isingLineBinomialKernel_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLineBinomialKernel_succ_eq
  {t : Nat}
  {x y : Int} :
-- imply
  isingLineBinomialKernel (t + 1) x y = (isingLineBinomialKernel t (x - 1) y + isingLineBinomialKernel t (x + 1) y) / 2 := by
-- proof
  apply StatMech.Universality.isingLineBinomialKernel_succ t x y

/--
[isingLineBinomialKernel_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLineBinomialKernel_nonneg_eq
  {t : Nat}
  {x y : Int} :
-- imply
  0 ≤ isingLineBinomialKernel t x y := by
-- proof
  apply StatMech.Universality.isingLineBinomialKernel_nonneg t x y

/--
[isingLineBinomialKernel_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLineBinomialKernel_sq_le_eq
  {t : Nat}
  {x y : Int} :
-- imply
  isingLineBinomialKernel t x y ^ 2 ≤ 2 / (t + 1 : Real) := by
-- proof
  apply StatMech.Universality.isingLineBinomialKernel_sq_le t x y

/--
[isingLeapfrogFreeKernel_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogFreeKernel_le_eq
  {t : Nat}
  {p q : IsingLeapfrogPlane} :
-- imply
  isingLeapfrogFreeKernel t p q ≤ 2 / (t + 1 : Real) := by
-- proof
  apply StatMech.Universality.isingLeapfrogFreeKernel_le t p q

/--
[isingLeapfrogKilledKernel_le_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogKilledKernel_le_free_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogKilledKernel R t p q ≤ isingLeapfrogFreeKernel t (isingLeapfrogBoxToPlane p) (isingLeapfrogBoxToPlane q) := by
-- proof
  apply StatMech.Universality.isingLeapfrogKilledKernel_le_free R t p q

/--
[isingLeapfrogKilledKernel_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogKilledKernel_le_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogKilledKernel R t p q ≤ 2 / (t + 1 : Real) := by
-- proof
  apply StatMech.Universality.isingLeapfrogKilledKernel_le R t p q

/--
[isingLeapfrogKilledKernel_diffusive_abs_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma isingLeapfrogKilledKernel_diffusive_abs_sub_le_eq
  {R ρ : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hρ : 0 < ρ) :
-- imply
  |isingLeapfrogKilledKernel R (ρ * ρ) p q - isingLeapfrogKilledKernel R (ρ * ρ + 1) p' q| ≤ 4 / (ρ : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.isingLeapfrogKilledKernel_diffusive_abs_sub_le R ρ p p' q hρ

/--
[IsingLeapfrogDiffusiveExitInputs.kernelInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma kernelInputs_eq
  {A B : Real}
-- given
  (hAB : IsingLeapfrogDiffusiveExitInputs A B) :
-- imply
  IsingLeapfrogDiffusiveKernelInputs (A + 4) B := by
-- proof
  apply StatMech.Universality.IsingLeapfrogDiffusiveExitInputs.kernelInputs hAB

/--
[IsingLeapfrogDiffusiveExitInputs.gradientBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean)
-/
@[path]
private lemma gradientBound_eq
  {A B : Real}
-- given
  (hAB : IsingLeapfrogDiffusiveExitInputs A B) :
-- imply
  IsingLeapfrogDiffusiveGradientBound ((A + 4) * B) := by
-- proof
  apply StatMech.Universality.IsingLeapfrogDiffusiveExitInputs.gradientBound hAB


-- created on 2026-10-23
