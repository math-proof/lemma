import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialRegularity
open StatMech StatMech.Universality


/--
[fkIsingSquareBoundaryRadialPatchFullObservable_quad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservable_quad_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (heven : Even (i + j)) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩) (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩) (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservable_quad n m i j hn hm hi0 hi1 hj0 hj1 heven

/--
[fkIsingSquareBoundaryRadialPatchFullObservable_quad_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservable_quad_of_odd_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (hodd : ¬ Even (i + j)) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩) (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩) (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩) (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservable_quad_of_odd n m i j hn hm hi0 hi1 hj0 hj1 hodd

/--
[fkIsingSquareBoundaryRadialPatchFullObservableExtension_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservableExtension_apply_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi : i < m)
  (hj : j < m) :
-- imply
  fkIsingSquareBoundaryRadialPatchFullObservableExtension n m hn hm i j = fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, hi⟩ ⟨j, hj⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservableExtension_apply n m hn hm i j hi hj

/--
[fkIsingSquareBoundaryRadialPatchFullObservable_cellCR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservable_cellCR_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi : i + 2 < m)
  (hj : j + 2 < m) :
-- imply
  IsingCellCRAt (fkIsingSquareBoundaryRadialPatchFullObservableExtension n m hn hm) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservable_cellCR n m i j hn hm hi hj

/--
[fkIsingSquareBoundaryRadialPatchFullObservable_leapfrog_harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservable_leapfrog_harmonic_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi : i + 3 < m)
  (hj : j + 3 < m) :
-- imply
  fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩ + fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j + 2, by omega⟩ + fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i + 2, by omega⟩ ⟨j, by omega⟩ + fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩ = 4 * fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservable_leapfrog_harmonic n m i j hn hm hi hj

/--
[fkIsingSquareBoundaryRadialPatchFullObservableWindow_harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservableWindow_harmonic_eq
  {n m baseI baseJ R : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m) :
-- imply
  IsingLeapfrogHarmonicOnBox R (fkIsingSquareBoundaryRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservableWindow_harmonic n m baseI baseJ R hn hm hfitI hfitJ

/--
[fkIsingSquareBoundaryRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le_diffusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le_diffusive_eq
  {n m baseI baseJ R rho : Nat}
  {mesh : Real}
  {p p' : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hmesh : 0 < mesh)
  (hrho : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  Complex.normSq (fkIsingSquareBoundaryRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p / (Real.sqrt (2 * mesh) : Complex) - fkIsingSquareBoundaryRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p' / (Real.sqrt (2 * mesh) : Complex)) ≤ (1032080 / (rho : Real) ^ 3) * ∑ q, Complex.normSq (fkIsingSquareBoundaryRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ q / (Real.sqrt (2 * mesh) : Complex)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le_diffusive n m baseI baseJ R rho mesh hn hm hfitI hfitJ hmesh p p' hrho hp hp' hpp'

/--
[fkIsingSquareBoundaryRadialPatchDeepVariation_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchDeepVariation_nonneg_eq
  {n m : Nat}
  {r : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  0 ≤ fkIsingSquareBoundaryRadialPatchDeepVariation n m hn hm hm2 r := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchDeepVariation_nonneg n m hn hm hm2 r

/--
[fkIsingSquareBoundaryRadialPatchDeepVariation_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchDeepVariation_le_eq
  {n m r : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r) :
-- imply
  fkIsingSquareBoundaryRadialPatchDeepVariation n m hn hm hm2 r ≤ 16 * (m : Real) ^ 2 / (r : Real) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchDeepVariation_le n m r hn hm hm2 hr

/--
[fkIsingSquareBoundaryRadialPatch_deepCell_physicalNormalized_energy_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatch_deepCell_physicalNormalized_energy_le_eq
  {n m : Nat}
  {mesh : Real}
  {r : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hmesh : 0 < mesh) :
-- imply
  mesh ^ 2 * ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r, Complex.normSq (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ / (Real.sqrt (2 * mesh) : Complex)) ≤ mesh * fkIsingSquareBoundaryRadialPatchDeepVariation n m hn hm hm2 r := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatch_deepCell_physicalNormalized_energy_le n m mesh hn hm hm2 hmesh r

/--
[fkIsingSquareBoundaryRadialPatchFullObservableWindow_deep_energy_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservableWindow_deep_energy_le_eq
  {n m baseI baseJ R : Nat}
  {mesh : Real}
  {r : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hmesh : 0 < mesh)
  (hdeep : ∀ p : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r) :
-- imply
  mesh ^ 2 * ∑ p : IsingLeapfrogBox R, Complex.normSq (fkIsingSquareBoundaryRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p / (Real.sqrt (2 * mesh) : Complex)) ≤ mesh * fkIsingSquareBoundaryRadialPatchDeepVariation n m hn hm hm2 r := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservableWindow_deep_energy_le n m baseI baseJ R mesh hn hm hm2 hfitI hfitJ hmesh r hdeep

/--
[fkIsingSquareBoundaryRadialPatchFullObservableWindow_deep_diffusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservableWindow_deep_diffusive_eq
  {n m baseI baseJ R rho : Nat}
  {mesh : Real}
  {r : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hmesh : 0 < mesh)
  (hdeep : ∀ q : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
  (hrho : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  mesh ^ 2 * Complex.normSq (fkIsingSquareBoundaryRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p / (Real.sqrt (2 * mesh) : Complex) - fkIsingSquareBoundaryRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p' / (Real.sqrt (2 * mesh) : Complex)) ≤ (1032080 / (rho : Real) ^ 3) * mesh * fkIsingSquareBoundaryRadialPatchDeepVariation n m hn hm hm2 r := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservableWindow_deep_diffusive n m baseI baseJ R rho mesh hn hm hm2 hfitI hfitJ hmesh r hdeep p p' hrho hp hp' hpp'

/--
[fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le_eq
  {n m baseI baseJ R rho : Nat}
  {mesh d H V : Real}
  {r : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hmesh : 0 < mesh)
  (hdeep : ∀ q : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
  (hV : fkIsingSquareBoundaryRadialPatchDeepVariation n m hn hm hm2 r ≤ V)
  (hd : 0 ≤ d)
  (hH : 0 ≤ H)
  (hradius : d ≤ mesh * (rho : Real))
  (hscale : 1032080 * V ≤ H ^ 2 * d ^ 3)
  (hrho : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  ‖fkIsingSquareBoundaryRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p / (Real.sqrt (2 * mesh) : Complex) - fkIsingSquareBoundaryRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p' / (Real.sqrt (2 * mesh) : Complex)‖ ≤ mesh * H := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le n m baseI baseJ R rho mesh d H V hn hm hm2 hfitI hfitJ hmesh r hdeep hV hd hH hradius hscale p p' hrho hp hp' hpp'

/--
[fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_halfScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_halfScale_eq
  {n m baseI baseJ R rho r : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hdeep : ∀ q : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
  (hmr : m ≤ 2 * r)
  (hmrho : m ≤ 2 * rho)
  (hrho : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  ‖fkIsingSquareBoundaryRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p / (Real.sqrt (2 * (1 / (m : Real))) : Complex) - fkIsingSquareBoundaryRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p' / (Real.sqrt (2 * (1 / (m : Real))) : Complex)‖ ≤ (1 / (m : Real)) * Real.sqrt (264212480 * (m : Real)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_halfScale n m baseI baseJ R rho r hn hm hm2 hr hfitI hfitJ hdeep hmr hmrho p p' hrho hp hp' hpp'


-- created on 2026-10-23
