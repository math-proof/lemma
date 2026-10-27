import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCheckerboard.Part4
open StatMech StatMech.Universality


/--
[fkIsingSquareRadialPatchPrimalGraph_laplacian_eq_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalGraph_laplacian_eq_diagonal_eq
  {n m i j : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (heven : Even (i + j)) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareRadialPatchPrimalGraph n m hm) (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base) ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), heven⟩ = fkIsingSquareRadialPatchDiagonalLaplacian (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalGraph_laplacian_eq_diagonal n m i j hn hm hmpos base hi0 hi1 hj0 hj1 heven

/--
[fkIsingSquareRadialPatchPrimalValue_superharmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalValue_superharmonicOn_eq
  {n m : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  IsingFiniteGraphSuperharmonicOn (fkIsingSquareRadialPatchPrimalGraph n m hm) (fkIsingSquareRadialPatchPrimalBoundary m) (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalValue_superharmonicOn n m hn hm hmpos base

/--
[fkIsingSquareRadialPatchDualGraph_laplacian_eq_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualGraph_laplacian_eq_diagonal_eq
  {n m i j : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (hodd : ¬ Even (i + j)) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareRadialPatchDualGraph m) (fkIsingSquareRadialPatchDualValue n m hn hm hmpos base) ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), hodd⟩ = fkIsingSquareRadialPatchDiagonalLaplacian (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualGraph_laplacian_eq_diagonal n m i j hn hm hmpos base hi0 hi1 hj0 hj1 hodd

/--
[fkIsingSquareRadialPatchDualValue_subharmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualValue_subharmonicOn_eq
  {n m : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  IsingFiniteGraphSubharmonicOn (fkIsingSquareRadialPatchDualGraph m) (fkIsingSquareRadialPatchDualBoundary m) (fkIsingSquareRadialPatchDualValue n m hn hm hmpos base) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualValue_subharmonicOn n m hn hm hmpos base

/--
[fkIsingSquareRadialPatchPrimalGraph_reachable_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalGraph_reachable_boundary_eq
  {n m : Nat}
-- given
  (hm : m ≤ n) :
-- imply
  ∀ p : FKIsingSquareRadialPatchPrimalNode m, ∃ b, fkIsingSquareRadialPatchPrimalBoundary m b ∧ (fkIsingSquareRadialPatchPrimalGraph n m hm).Reachable p b := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalGraph_reachable_boundary n m hm

/--
[fkIsingSquareRadialPatchDualGraph_reachable_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualGraph_reachable_boundary_eq
  {m : Nat} :
-- imply
  ∀ p : FKIsingSquareRadialPatchDualNode m, ∃ b, fkIsingSquareRadialPatchDualBoundary m b ∧ (fkIsingSquareRadialPatchDualGraph m).Reachable p b := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualGraph_reachable_boundary m

/--
[fkIsingSquareRadialPatchPrimal_harmonic_le_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimal_harmonic_le_value_eq
  {n m : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (harmonic : FKIsingSquareRadialPatchPrimalNode m → Real)
  (hharmonic : IsingFiniteGraphHarmonicOn (fkIsingSquareRadialPatchPrimalGraph n m hm) (fkIsingSquareRadialPatchPrimalBoundary m) harmonic)
  (hboundary : ∀ p, fkIsingSquareRadialPatchPrimalBoundary m p → harmonic p ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p) :
-- imply
  ∀ p, harmonic p ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimal_harmonic_le_value n m hn hm hmpos base harmonic hharmonic hboundary

/--
[fkIsingSquareRadialPatchDual_value_le_harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDual_value_le_harmonic_eq
  {n m : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (harmonic : FKIsingSquareRadialPatchDualNode m → Real)
  (hharmonic : IsingFiniteGraphHarmonicOn (fkIsingSquareRadialPatchDualGraph m) (fkIsingSquareRadialPatchDualBoundary m) harmonic)
  (hboundary : ∀ p, fkIsingSquareRadialPatchDualBoundary m p → fkIsingSquareRadialPatchDualValue n m hn hm hmpos base p ≤ harmonic p) :
-- imply
  ∀ p, fkIsingSquareRadialPatchDualValue n m hn hm hmpos base p ≤ harmonic p := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDual_value_le_harmonic n m hn hm hmpos base harmonic hharmonic hboundary

/--
[fkIsingSquareRadialPatchPrimitive_horizontal_even_le_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitive_horizontal_even_le_odd_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i + 1 < m)
  (hj : j < m)
  (heven : Even (i + j)) :
-- imply
  fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j ≤ fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitive_horizontal_even_le_odd n m hn hm hmpos i j hi hj heven

/--
[fkIsingSquareRadialPatchPrimitive_horizontal_even_le_odd_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitive_horizontal_even_le_odd_of_odd_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i + 1 < m)
  (hj : j < m)
  (hodd : ¬ Even (i + j)) :
-- imply
  fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j ≤ fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitive_horizontal_even_le_odd_of_odd n m hn hm hmpos i j hi hj hodd

/--
[fkIsingSquareRadialPatchPrimitive_vertical_even_le_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitive_vertical_even_le_odd_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j + 1 < m)
  (heven : Even (i + j)) :
-- imply
  fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j ≤ fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitive_vertical_even_le_odd n m hn hm hmpos i j hi hj heven

/--
[fkIsingSquareRadialPatchPrimitive_vertical_even_le_odd_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitive_vertical_even_le_odd_of_odd_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j + 1 < m)
  (hodd : ¬ Even (i + j)) :
-- imply
  fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) ≤ fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitive_vertical_even_le_odd_of_odd n m hn hm hmpos i j hi hj hodd

/--
[fkIsingSquareRadialPatch_checkerboard_dirichlet_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_checkerboard_dirichlet_sandwich_eq
  {n m : Nat}
  {base : Real}
  {primalHarmonic : FKIsingSquareRadialPatchPrimalNode m → Real}
  {dualHarmonic : FKIsingSquareRadialPatchDualNode m → Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hprimal : IsingFiniteGraphHarmonicOn (fkIsingSquareRadialPatchPrimalGraph n m hm) (fkIsingSquareRadialPatchPrimalBoundary m) primalHarmonic)
  (hdual : IsingFiniteGraphHarmonicOn (fkIsingSquareRadialPatchDualGraph m) (fkIsingSquareRadialPatchDualBoundary m) dualHarmonic)
  (hprimalBoundary : ∀ p, fkIsingSquareRadialPatchPrimalBoundary m p → primalHarmonic p = fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p)
  (hdualBoundary : ∀ p, fkIsingSquareRadialPatchDualBoundary m p → dualHarmonic p = fkIsingSquareRadialPatchDualValue n m hn hm hmpos base p) :
-- imply
  (∀ p, primalHarmonic p ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p) ∧ (∀ p, fkIsingSquareRadialPatchDualValue n m hn hm hmpos base p ≤ dualHarmonic p) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_checkerboard_dirichlet_sandwich n m hn hm hmpos base primalHarmonic dualHarmonic hprimal hdual hprimalBoundary hdualBoundary

/--
[fkIsingSquareRadialPatchPrimalDirichlet_harmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalDirichlet_harmonicOn_eq
  {n m : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  IsingFiniteGraphHarmonicOn (fkIsingSquareRadialPatchPrimalGraph n m hm) (fkIsingSquareRadialPatchPrimalBoundary m) (fkIsingSquareRadialPatchPrimalDirichlet n m hn hm hmpos base) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalDirichlet_harmonicOn n m hn hm hmpos base

/--
[fkIsingSquareRadialPatchPrimalDirichlet_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalDirichlet_boundary_eq
  {n m : Nat}
  {base : Real}
  {p : FKIsingSquareRadialPatchPrimalNode m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hp : fkIsingSquareRadialPatchPrimalBoundary m p) :
-- imply
  fkIsingSquareRadialPatchPrimalDirichlet n m hn hm hmpos base p = fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalDirichlet_boundary n m hn hm hmpos base p hp

/--
[fkIsingSquareRadialPatchDualDirichlet_harmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualDirichlet_harmonicOn_eq
  {n m : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  IsingFiniteGraphHarmonicOn (fkIsingSquareRadialPatchDualGraph m) (fkIsingSquareRadialPatchDualBoundary m) (fkIsingSquareRadialPatchDualDirichlet n m hn hm hm2 base) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualDirichlet_harmonicOn n m hn hm hm2 base

/--
[fkIsingSquareRadialPatchDualDirichlet_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualDirichlet_boundary_eq
  {n m : Nat}
  {base : Real}
  {p : FKIsingSquareRadialPatchDualNode m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hp : fkIsingSquareRadialPatchDualBoundary m p) :
-- imply
  fkIsingSquareRadialPatchDualDirichlet n m hn hm hm2 base p = fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualDirichlet_boundary n m hn hm hm2 base p hp

/--
[fkIsingSquareRadialPatch_constructed_dirichlet_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_constructed_dirichlet_sandwich_eq
  {n m : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  (∀ p, fkIsingSquareRadialPatchPrimalDirichlet n m hn hm (by omega) base p ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p) ∧ (∀ p, fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p ≤ fkIsingSquareRadialPatchDualDirichlet n m hn hm hm2 base p) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_constructed_dirichlet_sandwich n m hn hm hm2 base


-- created on 2026-10-23
