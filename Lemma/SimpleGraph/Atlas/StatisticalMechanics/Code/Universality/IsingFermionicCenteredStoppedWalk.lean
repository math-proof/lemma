import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicCenteredStoppedWalk
open StatMech StatMech.Universality


/--
[IsingLeapfrogHarmonicOnBox.norm_sub_le_kernelTimeL1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredStoppedWalk.lean)
-/
@[path]
private lemma norm_sub_le_kernelTimeL1_eq
  {R : Nat}
  {f : IsingLeapfrogBox R → Complex}
  {B : Real}
  {t t' : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hf : IsingLeapfrogHarmonicOnBox R f)
  (hB : ∀ q, ‖f q‖ ≤ B) :
-- imply
  ‖f p - f p'‖ ≤ B * ∑ q, := by
-- proof
  apply StatMech.Universality.IsingLeapfrogHarmonicOnBox.norm_sub_le_kernelTimeL1 hf B hB t t' p p'

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservable_norm_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredStoppedWalk.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservable_norm_le_two_eq
  {n : Nat}
  {i j : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  ‖fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j‖ ≤ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservable_norm_le_two n hn i j

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservable_leapfrog_harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredStoppedWalk.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservable_leapfrog_harmonic_eq
  {n i j : Nat}
-- given
  (hn : 0 < n)
  (hi : i + 3 < 2 * n)
  (hj : j + 3 < 2 * n) :
-- imply
  fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i, by omega⟩ ⟨j, by omega⟩ + fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i, by omega⟩ ⟨j + 2, by omega⟩ + fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i + 2, by omega⟩ ⟨j, by omega⟩ + fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩ = 4 * fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservable_leapfrog_harmonic n i j hn hi hj

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredStoppedWalk.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_harmonic_eq
  {n baseI baseJ R : Nat}
-- given
  (hn : 0 < n)
  (hfitI : baseI + R + 1 < 2 * n)
  (hfitJ : baseJ + R + 1 < 2 * n) :
-- imply
  IsingLeapfrogHarmonicOnBox R (fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow n baseI baseJ R hn hfitI hfitJ) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_harmonic n baseI baseJ R hn hfitI hfitJ

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredStoppedWalk.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le_eq
  {n baseI baseJ R rho : Nat}
  {mesh : Real}
  {p p' : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hfitI : baseI + R + 1 < 2 * n)
  (hfitJ : baseJ + R + 1 < 2 * n)
  (hmesh : 0 < mesh)
  (hrho : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  Complex.normSq (fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow n baseI baseJ R hn hfitI hfitJ p / (Real.sqrt (2 * mesh) : Complex) - fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow n baseI baseJ R hn hfitI hfitJ p' / (Real.sqrt (2 * mesh) : Complex)) ≤ (1032080 / (rho : Real) ^ 3) * ∑ q, Complex.normSq (fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow n baseI baseJ R hn hfitI hfitJ q / (Real.sqrt (2 * mesh) : Complex)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le n baseI baseJ R rho mesh hn hfitI hfitJ hmesh p p' hrho hp hp' hpp'

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_norm_sub_le_diffusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredStoppedWalk.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_norm_sub_le_diffusive_eq
  {n baseI baseJ R rho : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hfitI : baseI + R + 1 < 2 * n)
  (hfitJ : baseJ + R + 1 < 2 * n)
  (hrho : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  ‖fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow n baseI baseJ R hn hfitI hfitJ p - fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow n baseI baseJ R hn hfitI hfitJ p'‖ ≤ 304 / (rho : Real) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_norm_sub_le_diffusive n baseI baseJ R rho hn hfitI hfitJ p p' hrho hp hp' hpp'

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_physicalNormalized_norm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredStoppedWalk.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_physicalNormalized_norm_sub_le_eq
  {n baseI baseJ R rho : Nat}
  {mesh : Real}
  {p p' : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hfitI : baseI + R + 1 < 2 * n)
  (hfitJ : baseJ + R + 1 < 2 * n)
  (hmesh : 0 < mesh)
  (hrho : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  ‖fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow n baseI baseJ R hn hfitI hfitJ p / (Real.sqrt (2 * mesh) : Complex) - fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow n baseI baseJ R hn hfitI hfitJ p' / (Real.sqrt (2 * mesh) : Complex)‖ ≤ 304 / ((rho : Real) * Real.sqrt (2 * mesh)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_physicalNormalized_norm_sub_le n baseI baseJ R rho mesh hn hfitI hfitJ hmesh p p' hrho hp hp' hpp'


-- created on 2026-10-23
