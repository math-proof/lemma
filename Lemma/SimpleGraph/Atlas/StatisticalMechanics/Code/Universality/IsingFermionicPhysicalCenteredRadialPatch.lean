import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
open StatMech StatMech.Universality


/--
[fkIsingSquareCenteredRadialPatchDirection_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareCenteredRadialPatchDirection_available_eq
  {n : Nat}
  {i j : Fin (2 * n)} :
-- imply
  fkIsingSquareDirectionAvailable n (fkIsingSquareCenteredRadialPatchVertex n i j) (fkIsingSquareCenteredRadialPatchDirection i.1 j.1) := by
-- proof
  apply StatMech.Universality.fkIsingSquareCenteredRadialPatchDirection_available n i j

/--
[fkIsingSquareCenteredRadialPatchEdge_eq_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareCenteredRadialPatchEdge_eq_east_eq
  {n : Nat}
  {i j : Fin (2 * n)}
-- given
  (h : Even (i.1 + j.1)) :
-- imply
  fkIsingSquareCenteredRadialPatchEdge n i j = fkIsingSquareDirectionEdge n (fkIsingSquareCenteredRadialPatchVertex n i j) .east (by simpa [fkIsingSquareCenteredRadialPatchDirection, h] using fkIsingSquareCenteredRadialPatchDirection_available n i j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareCenteredRadialPatchEdge_eq_east n i j h

/--
[fkIsingSquareCenteredRadialPatchEdge_eq_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareCenteredRadialPatchEdge_eq_north_eq
  {n : Nat}
  {i j : Fin (2 * n)}
-- given
  (h : ¬ Even (i.1 + j.1)) :
-- imply
  fkIsingSquareCenteredRadialPatchEdge n i j = fkIsingSquareDirectionEdge n (fkIsingSquareCenteredRadialPatchVertex n i j) .north (by simpa [fkIsingSquareCenteredRadialPatchDirection, h] using fkIsingSquareCenteredRadialPatchDirection_available n i j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareCenteredRadialPatchEdge_eq_north n i j h

/--
[fkIsingSquareCenteredRadialPatchEdge_add_side_eq_radialPatchEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareCenteredRadialPatchEdge_add_side_eq_radialPatchEdge_eq
  {n m a b : Nat}
-- given
  (hm : m ≤ n)
  (ha : a < m)
  (hb : b < m) :
-- imply
  fkIsingSquareCenteredRadialPatchEdge n ⟨n + a, by omega⟩ ⟨n + b, by omega⟩ = fkIsingSquareRadialPatchEdge n m hm ⟨a, ha⟩ ⟨b, hb⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareCenteredRadialPatchEdge_add_side_eq_radialPatchEdge n m a b hm ha hb

/--
[isingReflectedCenteredRadialGridPosition_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma isingReflectedCenteredRadialGridPosition_eq_eq
  {mesh : Real}
  {n i j : Nat} :
-- imply
  isingReflectedCenteredRadialGridPosition mesh n i j = (mesh * (((i : Real) + (j : Real) + 1) / 2 - n) : Real) + (mesh * (((j : Real) - (i : Real)) / 2) : Real) * Complex.I := by
-- proof
  apply StatMech.Universality.isingReflectedCenteredRadialGridPosition_eq mesh n i j

/--
[isingReflectedCenteredRadialGridPosition_succ_i](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma isingReflectedCenteredRadialGridPosition_succ_i_eq
  {mesh : Real}
  {n i j : Nat} :
-- imply
  isingReflectedCenteredRadialGridPosition mesh n (i + 1) j = isingReflectedCenteredRadialGridPosition mesh n i j + (mesh : Complex) / 2 * (1 - Complex.I) := by
-- proof
  apply StatMech.Universality.isingReflectedCenteredRadialGridPosition_succ_i mesh n i j

/--
[isingReflectedCenteredRadialGridPosition_succ_j](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma isingReflectedCenteredRadialGridPosition_succ_j_eq
  {mesh : Real}
  {n i j : Nat} :
-- imply
  isingReflectedCenteredRadialGridPosition mesh n i (j + 1) = isingReflectedCenteredRadialGridPosition mesh n i j + (mesh : Complex) / 2 * (1 + Complex.I) := by
-- proof
  apply StatMech.Universality.isingReflectedCenteredRadialGridPosition_succ_j mesh n i j

/--
[isingReflectedCenteredRadialGridPosition_succ_both](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma isingReflectedCenteredRadialGridPosition_succ_both_eq
  {mesh : Real}
  {n i j : Nat} :
-- imply
  isingReflectedCenteredRadialGridPosition mesh n (i + 1) (j + 1) = isingReflectedCenteredRadialGridPosition mesh n i j + mesh := by
-- proof
  apply StatMech.Universality.isingReflectedCenteredRadialGridPosition_succ_both mesh n i j

/--
[isingReflectedCenteredRadialGridPosition_vertical_macroStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma isingReflectedCenteredRadialGridPosition_vertical_macroStep_eq
  {mesh : Real}
  {n i j : Nat} :
-- imply
  isingReflectedCenteredRadialGridPosition mesh n i (j + 1) = isingReflectedCenteredRadialGridPosition mesh n (i + 1) j + mesh * Complex.I := by
-- proof
  apply StatMech.Universality.isingReflectedCenteredRadialGridPosition_vertical_macroStep mesh n i j

/--
[isingReflectedCenteredRadialGridPosition_diagonal_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma isingReflectedCenteredRadialGridPosition_diagonal_add_eq
  {mesh : Real}
  {n i j k : Nat} :
-- imply
  isingReflectedCenteredRadialGridPosition mesh n (i + k) (j + k) = isingReflectedCenteredRadialGridPosition mesh n i j + (k : Real) * mesh := by
-- proof
  apply StatMech.Universality.isingReflectedCenteredRadialGridPosition_diagonal_add mesh n i j k

/--
[isingReflectedCenteredRadialGridPosition_antidiagonal_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma isingReflectedCenteredRadialGridPosition_antidiagonal_add_eq
  {mesh : Real}
  {n i j N k : Nat}
-- given
  (hk : k ≤ N) :
-- imply
  isingReflectedCenteredRadialGridPosition mesh n (i + (N - k)) (j + k) = isingReflectedCenteredRadialGridPosition mesh n (i + N) j + ((k : Real) * mesh) * Complex.I := by
-- proof
  apply StatMech.Universality.isingReflectedCenteredRadialGridPosition_antidiagonal_add mesh n i j N k hk

/--
[isingReflectedCenteredRadialGridPosition_diagonal_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma isingReflectedCenteredRadialGridPosition_diagonal_sub_eq
  {mesh : Real}
  {n i j N M k : Nat}
-- given
  (hkN : k ≤ N)
  (hkM : k ≤ M) :
-- imply
  isingReflectedCenteredRadialGridPosition mesh n (i + (N - k)) (j + (M - k)) = isingReflectedCenteredRadialGridPosition mesh n (i + N) (j + M) - (k : Real) * mesh := by
-- proof
  apply StatMech.Universality.isingReflectedCenteredRadialGridPosition_diagonal_sub mesh n i j N M k hkN hkM

/--
[isingReflectedCenteredRadialGridPosition_antidiagonal_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma isingReflectedCenteredRadialGridPosition_antidiagonal_sub_eq
  {mesh : Real}
  {n i j N k : Nat}
-- given
  (hk : k ≤ N) :
-- imply
  isingReflectedCenteredRadialGridPosition mesh n (i + k) (j + (N - k)) = isingReflectedCenteredRadialGridPosition mesh n i (j + N) - ((k : Real) * mesh) * Complex.I := by
-- proof
  apply StatMech.Universality.isingReflectedCenteredRadialGridPosition_antidiagonal_sub mesh n i j N k hk

/--
[isingCenteredRadialGridPosition_eq_scaledCarrierPosition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma isingCenteredRadialGridPosition_eq_scaledCarrierPosition_eq
  {n : Nat}
  {mesh : Real}
  {i j : Fin (2 * n)}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n) :
-- imply
  isingCenteredRadialGridPosition mesh n i.1 j.1 = (mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn (.dart (fkIsingSquareCenteredRadialPatchEdge n i j, s)) := by
-- proof
  apply StatMech.Universality.isingCenteredRadialGridPosition_eq_scaledCarrierPosition n hn mesh i j s

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_apply_eq
  {n : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hi : i < 2 * n)
  (hj : j < 2 * n) :
-- imply
  fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn i j = fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i, hi⟩ ⟨j, hj⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_apply n hn i j hi hj

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_eq
  {n I J : Nat}
-- given
  (hn : 0 < n)
  (hI0 : 0 < I)
  (hI1 : I + 1 < 2 * n)
  (hJ0 : 0 < J)
  (hJ1 : J + 1 < 2 * n)
  (heven : Even (I + J)) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I - 1, by omega⟩ ⟨J, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I, by omega⟩ ⟨J - 1, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I, by omega⟩ ⟨J, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad n I J hn hI0 hI1 hJ0 hJ1 heven

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_even_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_even_available_eq
  {n I J : Nat}
-- given
  (hn : 0 < n)
  (hI0 : 0 < I)
  (hI : I < 2 * n)
  (hJ0 : 0 < J)
  (hJ : J < 2 * n)
  (heven : Even (I + J))
  (heast : fkIsingSquareDirectionAvailable n (fkIsingSquareCenteredRadialPatchVertex n ⟨I, hI⟩ ⟨J, hJ⟩) .east)
  (hnorth : fkIsingSquareDirectionAvailable n (fkIsingSquareCenteredRadialPatchVertex n ⟨I, hI⟩ ⟨J, hJ⟩) .north)
  (hwest : fkIsingSquareDirectionAvailable n (fkIsingSquareCenteredRadialPatchVertex n ⟨I, hI⟩ ⟨J, hJ⟩) .west)
  (hsouth : fkIsingSquareDirectionAvailable n (fkIsingSquareCenteredRadialPatchVertex n ⟨I, hI⟩ ⟨J, hJ⟩) .south) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I - 1, by omega⟩ ⟨J, hJ⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I, hI⟩ ⟨J - 1, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I, hI⟩ ⟨J, hJ⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_even_available n I J hn hI0 hI hJ0 hJ heven heast hnorth hwest hsouth

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_even_eq
  {n J : Nat}
-- given
  (hn : 0 < n)
  (hJ0 : 0 < J)
  (hJ : J < 2 * n)
  (heven : Even ((2 * n - 1) + J)) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨2 * n - 2, by omega⟩ ⟨J, hJ⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨2 * n - 2, by omega⟩ ⟨J - 1, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨2 * n - 1, by omega⟩ ⟨J - 1, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨2 * n - 1, by omega⟩ ⟨J, hJ⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_even n J hn hJ0 hJ heven

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_even_eq
  {n I : Nat}
-- given
  (hn : 0 < n)
  (hI0 : 0 < I)
  (hI : I < 2 * n)
  (heven : Even (I + (2 * n - 1))) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I - 1, by omega⟩ ⟨2 * n - 1, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I - 1, by omega⟩ ⟨2 * n - 2, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I, hI⟩ ⟨2 * n - 2, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I, hI⟩ ⟨2 * n - 1, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_even n I hn hI0 hI heven

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_odd_eq
  {n I J : Nat}
-- given
  (hn : 0 < n)
  (hI0 : 0 < I)
  (hI1 : I + 1 < 2 * n)
  (hJ0 : 0 < J)
  (hJ1 : J + 1 < 2 * n)
  (hodd : ¬ Even (I + J)) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I, by omega⟩ ⟨J - 1, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I, by omega⟩ ⟨J, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I - 1, by omega⟩ ⟨J, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_odd n I J hn hI0 hI1 hJ0 hJ1 hodd

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_odd_faceInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_odd_faceInterior_eq
  {n I J : Nat}
-- given
  (hn : 0 < n)
  (hI0 : 0 < I)
  (hI : I < 2 * n)
  (hJ0 : 0 < J)
  (hJ : J < 2 * n)
  (hodd : ¬ Even (I + J))
  (hwest : 0 < centeredRadialHalf I J - 1)
  (heast : centeredRadialHalf I J - 1 + 1 < 2 * n)
  (hsouth : 0 < n + I - centeredRadialHalf I J)
  (hnorth : n + I - centeredRadialHalf I J + 1 < 2 * n) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I, hI⟩ ⟨J - 1, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I, hI⟩ ⟨J, hJ⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I - 1, by omega⟩ ⟨J, hJ⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_odd_faceInterior n I J hn hI0 hI hJ0 hJ hodd hwest heast hsouth hnorth

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_odd_eq
  {n J : Nat}
-- given
  (hn : 0 < n)
  (hJ0 : 0 < J)
  (hJ : J < 2 * n)
  (hodd : ¬ Even ((2 * n - 1) + J)) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨2 * n - 1, by omega⟩ ⟨J - 1, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨2 * n - 1, by omega⟩ ⟨J, hJ⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨2 * n - 2, by omega⟩ ⟨J, hJ⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨2 * n - 2, by omega⟩ ⟨J - 1, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_odd n J hn hJ0 hJ hodd

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_odd_eq
  {n I : Nat}
-- given
  (hn : 0 < n)
  (hI0 : 0 < I)
  (hI : I < 2 * n)
  (hodd : ¬ Even (I + (2 * n - 1))) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I, hI⟩ ⟨2 * n - 2, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I, hI⟩ ⟨2 * n - 1, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I - 1, by omega⟩ ⟨2 * n - 1, by omega⟩) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨I - 1, by omega⟩ ⟨2 * n - 2, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_odd n I hn hI0 hI hodd

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR_eq
  {n i j : Nat}
-- given
  (hn : 0 < n)
  (hi : i + 2 < 2 * n)
  (hj : j + 2 < 2 * n) :
-- imply
  IsingCellCRAt (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR n i j hn hi hj

/--
[isingReflectedCenteredRadialGridCellPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma isingReflectedCenteredRadialGridCellPoint_eq_eq
  {mesh : Real}
  {n i j : Nat}
  {x y : Real} :
-- imply
  isingReflectedCenteredRadialGridCellPoint mesh n i j x y = isingReflectedCenteredRadialGridPosition mesh n i j + (x : Complex) * ((mesh : Complex) / 2 * (1 - Complex.I)) + (y : Complex) * ((mesh : Complex) / 2 * (1 + Complex.I)) := by
-- proof
  apply StatMech.Universality.isingReflectedCenteredRadialGridCellPoint_eq mesh n i j x y

/--
[finiteCenteredRadialGridInterpolant_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma finiteCenteredRadialGridInterpolant_continuous_eq
  {n : Nat}
  {mesh : Real}
-- given
  (value : Fin (2 * n) -> Fin (2 * n) -> Complex) :
-- imply
  Continuous (finiteCenteredRadialGridInterpolant n mesh value) := by
-- proof
  apply StatMech.Universality.finiteCenteredRadialGridInterpolant_continuous n mesh value

/--
[finiteCenteredRadialGridInterpolant_position](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma finiteCenteredRadialGridInterpolant_position_eq
  {n : Nat}
  {mesh : Real}
  {i j : Fin (2 * n)}
-- given
  (hmesh : mesh ≠ 0)
  (value : Fin (2 * n) -> Fin (2 * n) -> Complex) :
-- imply
  finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridPosition mesh n i.1 j.1) = value i j := by
-- proof
  apply StatMech.Universality.finiteCenteredRadialGridInterpolant_position n mesh hmesh value i j

/--
[finiteCenteredRadialGridInterpolant_cellPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma finiteCenteredRadialGridInterpolant_cellPoint_eq
  {n : Nat}
  {mesh : Real}
  {i j : Nat}
  {x y : Real}
-- given
  (hmesh : mesh ≠ 0)
  (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
  (hi : i + 1 < 2 * n)
  (hj : j + 1 < 2 * n)
  (hx0 : 0 ≤ x)
  (hx1 : x ≤ 1)
  (hy0 : 0 ≤ y)
  (hy1 : y ≤ 1) :
-- imply
  finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n i j x y) = complexBilinearCell (value ⟨i, by omega⟩ ⟨j, by omega⟩) (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) x y := by
-- proof
  apply StatMech.Universality.finiteCenteredRadialGridInterpolant_cellPoint n mesh hmesh value i j hi hj x y hx0 hx1 hy0 hy1

/--
[fkIsingSquareBoundaryCenteredRadialPatchInterpolant_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchInterpolant_continuous_eq
  {n : Nat}
  {mesh : Real}
-- given
  (hn : 0 < n) :
-- imply
  Continuous (fkIsingSquareBoundaryCenteredRadialPatchInterpolant n hn mesh) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchInterpolant_continuous n hn mesh

/--
[fkIsingSquareBoundaryCenteredRadialPatchInterpolant_position](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchInterpolant_position_eq
  {n : Nat}
  {mesh : Real}
  {i j : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hmesh : mesh ≠ 0) :
-- imply
  fkIsingSquareBoundaryCenteredRadialPatchInterpolant n hn mesh (isingCenteredRadialGridPosition mesh n i.1 j.1) = fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j / (Real.sqrt (2 * mesh) : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchInterpolant_position n hn mesh hmesh i j

/--
[fkIsingSquareBoundaryCenteredRadialPatchInterpolant_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchInterpolant_projection_eq
  {n : Nat}
  {mesh : Real}
  {i j : Fin (2 * n)}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (hmesh : 0 < mesh)
  (he : (fkIsingSquareCenteredRadialPatchEdge n i j).1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
-- imply
  isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquareCenteredRadialPatchEdge n i j, s))) (fkIsingSquareBoundaryCenteredRadialPatchInterpolant n hn mesh (isingCenteredRadialGridPosition mesh n i.1 j.1)) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquareCenteredRadialPatchEdge n i j, s)) / (Real.sqrt (2 * mesh) : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchInterpolant_projection n hn mesh hmesh i j he s

/--
[fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant_continuous_eq
  {n : Nat}
  {gridScale normalizationScale : Real}
-- given
  (hn : 0 < n) :
-- imply
  Continuous (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant n hn gridScale normalizationScale) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant_continuous n hn gridScale normalizationScale

/--
[fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant_position](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant_position_eq
  {n : Nat}
  {gridScale normalizationScale : Real}
  {i j : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hgridScale : gridScale ≠ 0) :
-- imply
  fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant n hn gridScale normalizationScale (isingCenteredRadialGridPosition gridScale n i.1 j.1) = fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j / (Real.sqrt (2 * normalizationScale) : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant_position n hn gridScale normalizationScale hgridScale i j

/--
[fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_continuous_eq
  {n : Nat}
  {gridScale normalizationScale : Real}
-- given
  (hn : 0 < n) :
-- imply
  Continuous (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant n hn gridScale normalizationScale) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_continuous n hn gridScale normalizationScale

/--
[fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_cellPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_cellPoint_eq
  {n i j : Nat}
  {gridScale normalizationScale : Real}
  {x y : Real}
-- given
  (hn : 0 < n)
  (hgridScale : gridScale ≠ 0)
  (hi : i + 1 < 2 * n)
  (hj : j + 1 < 2 * n)
  (hx0 : 0 ≤ x)
  (hx1 : x ≤ 1)
  (hy0 : 0 ≤ y)
  (hy1 : y ≤ 1) :
-- imply
  fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant n hn gridScale normalizationScale ((starRingEnd Complex) (isingCenteredRadialGridCellPoint gridScale n i j x y)) = complexBilinearCell (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i, by omega⟩ ⟨j, by omega⟩ / (Real.sqrt (2 * normalizationScale) : Complex)) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i + 1, by omega⟩ ⟨j, by omega⟩ / (Real.sqrt (2 * normalizationScale) : Complex)) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i, by omega⟩ ⟨j + 1, by omega⟩ / (Real.sqrt (2 * normalizationScale) : Complex)) (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ / (Real.sqrt (2 * normalizationScale) : Complex)) x y := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_cellPoint n i j hn gridScale normalizationScale hgridScale hi hj x y hx0 hx1 hy0 hy1

/--
[fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_position](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_position_eq
  {n : Nat}
  {gridScale normalizationScale : Real}
  {i j : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hgridScale : gridScale ≠ 0) :
-- imply
  fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant n hn gridScale normalizationScale ((starRingEnd Complex) (isingCenteredRadialGridPosition gridScale n i.1 j.1)) = fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j / (Real.sqrt (2 * normalizationScale) : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_position n hn gridScale normalizationScale hgridScale i j


-- created on 2026-10-23
