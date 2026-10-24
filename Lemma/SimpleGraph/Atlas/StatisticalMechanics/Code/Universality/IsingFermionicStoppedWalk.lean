import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk
open StatMech StatMech.Universality


/--
[isingLeapfrogStoppedKernel_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_succ_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedKernel R (t + 1) p q = if hp : isingLeapfrogBoxBoundary R p then isingLeapfrogStoppedKernel R t p q else (isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p) q + isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p hp) q + isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p hp) q + isingLeapfrogStoppedKernel R t (isingLeapfrogNE R p hp) q) / 4 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_succ R t p q

/--
[isingLeapfrogStoppedMean_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedMean_zero_eq
  {R : Nat}
  {f : IsingLeapfrogBox R → Complex}
  {p : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedMean R 0 f p = f p := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedMean_zero R f p

/--
[isingLeapfrogStoppedMean_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedMean_succ_eq
  {R t : Nat}
  {f : IsingLeapfrogBox R → Complex}
  {p : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedMean R (t + 1) f p = if hp : isingLeapfrogBoxBoundary R p then isingLeapfrogStoppedMean R t f p else (isingLeapfrogStoppedMean R t f (isingLeapfrogSW R p) + isingLeapfrogStoppedMean R t f (isingLeapfrogSE R p hp) + isingLeapfrogStoppedMean R t f (isingLeapfrogNW R p hp) + isingLeapfrogStoppedMean R t f (isingLeapfrogNE R p hp)) / 4 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedMean_succ R t f p

/--
[isingLeapfrogStoppedKernel_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_nonneg_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  0 ≤ isingLeapfrogStoppedKernel R t p q := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_nonneg R t p q

/--
[isingLeapfrogStoppedKernel_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_sum_eq_one_eq
  {R t : Nat}
  {p : IsingLeapfrogBox R} :
-- imply
  ∑ q, isingLeapfrogStoppedKernel R t p q = 1 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_sum_eq_one R t p

/--
[isingLeapfrogStoppedKernel_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_le_one_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedKernel R t p q ≤ 1 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_le_one R t p q

/--
[isingLeapfrogStoppedKernel_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_add_eq
  {R t s : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedKernel R (t + s) p q = ∑ r, isingLeapfrogStoppedKernel R t p r * isingLeapfrogStoppedKernel R s r q := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_add R t s p q

/--
[isingLeapfrogStoppedKernel_l1_add_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_l1_add_le_eq
  {R t t' s : Nat}
  {p p' : IsingLeapfrogBox R} :
-- imply
  (∑ q, |isingLeapfrogStoppedKernel R (t + s) p q - isingLeapfrogStoppedKernel R (t' + s) p' q|) ≤ ∑ r, := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_l1_add_le R t t' s p p'

/--
[isingLeapfrogStoppedKernel_of_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_of_boundary_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R}
-- given
  (hp : isingLeapfrogBoxBoundary R p) :
-- imply
  isingLeapfrogStoppedKernel R t p q = if p = q then 1 else 0 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_of_boundary R t p q hp

/--
[isingLeapfrogStoppedKernel_boundary_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_boundary_mono_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R}
-- given
  (hq : isingLeapfrogBoxBoundary R q) :
-- imply
  isingLeapfrogStoppedKernel R t p q ≤ isingLeapfrogStoppedKernel R (t + 1) p q := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_boundary_mono R t p q hq

/--
[isingLeapfrogStoppedBoundaryMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedBoundaryMass_nonneg_eq
  {R t : Nat}
  {p : IsingLeapfrogBox R} :
-- imply
  0 ≤ isingLeapfrogStoppedBoundaryMass R t p := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedBoundaryMass_nonneg R t p

/--
[isingLeapfrogStoppedBoundaryMass_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedBoundaryMass_zero_eq
  {R : Nat}
  {p : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedBoundaryMass R 0 p = if isingLeapfrogBoxBoundary R p then 1 else 0 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedBoundaryMass_zero R p

/--
[isingLeapfrogStoppedBoundaryMass_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedBoundaryMass_succ_eq
  {R t : Nat}
  {p : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedBoundaryMass R (t + 1) p = if hp : isingLeapfrogBoxBoundary R p then isingLeapfrogStoppedBoundaryMass R t p else (isingLeapfrogStoppedBoundaryMass R t (isingLeapfrogSW R p) + isingLeapfrogStoppedBoundaryMass R t (isingLeapfrogSE R p hp) + isingLeapfrogStoppedBoundaryMass R t (isingLeapfrogNW R p hp) + isingLeapfrogStoppedBoundaryMass R t (isingLeapfrogNE R p hp)) / 4 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedBoundaryMass_succ R t p

/--
[isingLeapfrogStoppedBoundaryMass_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedBoundaryMass_mono_eq
  {R t : Nat}
  {p : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedBoundaryMass R t p ≤ isingLeapfrogStoppedBoundaryMass R (t + 1) p := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedBoundaryMass_mono R t p

/--
[IsingLeapfrogHarmonicOnBox.stoppedMean_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma stoppedMean_eq_eq
  {R : Nat}
  {f : IsingLeapfrogBox R → Complex}
  {t : Nat}
  {p : IsingLeapfrogBox R}
-- given
  (hf : IsingLeapfrogHarmonicOnBox R f) :
-- imply
  isingLeapfrogStoppedMean R t f p = f p := by
-- proof
  apply StatMech.Universality.IsingLeapfrogHarmonicOnBox.stoppedMean_eq hf t p

/--
[isingLeapfrogStoppedKernelTimeGradientSq_sameTime](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernelTimeGradientSq_sameTime_eq
  {R t : Nat}
  {p p' : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedKernelTimeGradientSq R t t p p' = isingLeapfrogStoppedKernelGradientSq R t p p' := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernelTimeGradientSq_sameTime R t p p'

/--
[isingLeapfrogStoppedKernelTimeGradientSq_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernelTimeGradientSq_le_two_eq
  {R t t' : Nat}
  {p p' : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedKernelTimeGradientSq R t t' p p' ≤ 2 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernelTimeGradientSq_le_two R t t' p p'

/--
[isingLeapfrogStoppedKernelTimeGradientSq_le_mul_l1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernelTimeGradientSq_le_mul_l1_eq
  {R t t' : Nat}
  {p p' : IsingLeapfrogBox R}
  {A : Real}
-- given
  (hpoint : ∀ q, |isingLeapfrogStoppedKernel R t p q - isingLeapfrogStoppedKernel R t' p' q| ≤ A) :
-- imply
  isingLeapfrogStoppedKernelTimeGradientSq R t t' p p' ≤ A * ∑ q, := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernelTimeGradientSq_le_mul_l1 R t t' p p' A hpoint

/--
[IsingLeapfrogHarmonicOnBox.normSq_sub_le_kernelGradient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma normSq_sub_le_kernelGradient_eq
  {R : Nat}
  {f : IsingLeapfrogBox R → Complex}
  {t : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hf : IsingLeapfrogHarmonicOnBox R f) :
-- imply
  Complex.normSq (f p - f p') ≤ isingLeapfrogStoppedKernelGradientSq R t p p' * ∑ q, Complex.normSq (f q) := by
-- proof
  apply StatMech.Universality.IsingLeapfrogHarmonicOnBox.normSq_sub_le_kernelGradient hf t p p'

/--
[IsingLeapfrogHarmonicOnBox.normSq_sub_le_kernelTimeGradient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma normSq_sub_le_kernelTimeGradient_eq
  {R : Nat}
  {f : IsingLeapfrogBox R → Complex}
  {t t' : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hf : IsingLeapfrogHarmonicOnBox R f) :
-- imply
  Complex.normSq (f p - f p') ≤ isingLeapfrogStoppedKernelTimeGradientSq R t t' p p' * ∑ q, Complex.normSq (f q) := by
-- proof
  apply StatMech.Universality.IsingLeapfrogHarmonicOnBox.normSq_sub_le_kernelTimeGradient hf t t' p p'

/--
[IsingLeapfrogDiffusiveKernelInputs.gradientBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma gradientBound_eq
  {A B : Real}
-- given
  (hAB : IsingLeapfrogDiffusiveKernelInputs A B) :
-- imply
  IsingLeapfrogDiffusiveGradientBound (A * B) := by
-- proof
  apply StatMech.Universality.IsingLeapfrogDiffusiveKernelInputs.gradientBound hAB

/--
[isingLeapfrogDiffusiveGradientBound_unitMargin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma isingLeapfrogDiffusiveGradientBound_unitMargin_eq
  {R : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (_hp : IsingLeapfrogInteriorMargin R 1 p)
  (_hp' : IsingLeapfrogInteriorMargin R 1 p')
  (_hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  isingLeapfrogStoppedKernelTimeGradientSq R 1 2 p p' ≤ (2 : Real) / (1 : Real) ^ 3 := by
-- proof
  apply StatMech.Universality.isingLeapfrogDiffusiveGradientBound_unitMargin R p p' _hp _hp' _hpp'

/--
[IsingLeapfrogHarmonicOnBox.normSq_sub_le_of_diffusiveGradient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma normSq_sub_le_of_diffusiveGradient_eq
  {C : Real}
  {R ρ : Nat}
  {f : IsingLeapfrogBox R → Complex}
  {p p' : IsingLeapfrogBox R}
-- given
  (hC : IsingLeapfrogDiffusiveGradientBound C)
  (hf : IsingLeapfrogHarmonicOnBox R f)
  (hρ : 0 < ρ)
  (hp : IsingLeapfrogInteriorMargin R ρ p)
  (hp' : IsingLeapfrogInteriorMargin R ρ p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  Complex.normSq (f p - f p') ≤ (C / (ρ : Real) ^ 3) * ∑ q, Complex.normSq (f q) := by
-- proof
  apply StatMech.Universality.IsingLeapfrogHarmonicOnBox.normSq_sub_le_of_diffusiveGradient hC hf p p' hρ hp hp' hpp'

/--
[fkIsingSquareRadialPatchFullObservableWindow_harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchFullObservableWindow_harmonic_eq
  {n m baseI baseJ R : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m) :
-- imply
  IsingLeapfrogHarmonicOnBox R (fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchFullObservableWindow_harmonic n m baseI baseJ R hn hm hfitI hfitJ

/--
[fkIsingSquareRadialPatchFullObservableWindow_normSq_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchFullObservableWindow_normSq_sub_le_eq
  {n m baseI baseJ R : Nat}
  {t : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m) :
-- imply
  Complex.normSq (fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p - fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p') ≤ isingLeapfrogStoppedKernelGradientSq R t p p' * ∑ q, Complex.normSq (fkIsingSquareRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ q) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchFullObservableWindow_normSq_sub_le n m baseI baseJ R hn hm hfitI hfitJ t p p'


-- created on 2026-10-23
