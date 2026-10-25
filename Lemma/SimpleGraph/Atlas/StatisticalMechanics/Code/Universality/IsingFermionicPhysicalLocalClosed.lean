import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalLocalClosed.Part2
open StatMech StatMech.Universality


/--
[conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq_eq
  {t z : Complex}
-- given
  (h : t * z ^ 2 = (Complex.normSq z : Complex)) :
-- imply
  (starRingEnd Complex) z = t * z := by
-- proof
  apply StatMech.Universality.conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq t z h

/--
[isingFermionic_horizontal_normSq_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma isingFermionic_horizontal_normSq_balance_eq
  {W E S N : Complex}
-- given
  (hW : (starRingEnd Complex) W = W)
  (hE : (starRingEnd Complex) E = -E)
  (hS : (starRingEnd Complex) S = Complex.I * S)
  (hN : (starRingEnd Complex) N = -Complex.I * N)
  (hcontour : W - E = Complex.I * (S - N)) :
-- imply
  Complex.normSq W + Complex.normSq E = Complex.normSq S + Complex.normSq N := by
-- proof
  apply StatMech.Universality.isingFermionic_horizontal_normSq_balance W E S N hW hE hS hN hcontour

/--
[isingFermionic_vertical_normSq_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma isingFermionic_vertical_normSq_balance_eq
  {W E S N : Complex}
-- given
  (hW : (starRingEnd Complex) W = -Complex.I * W)
  (hE : (starRingEnd Complex) E = Complex.I * E)
  (hS : (starRingEnd Complex) S = S)
  (hN : (starRingEnd Complex) N = -N)
  (hcontour : W - E = Complex.I * (S - N)) :
-- imply
  Complex.normSq W + Complex.normSq E = Complex.normSq S + Complex.normSq N := by
-- proof
  apply StatMech.Universality.isingFermionic_vertical_normSq_balance W E S N hW hE hS hN hcontour

/--
[isingFermionic_horizontal_sum_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma isingFermionic_horizontal_sum_balance_eq
  {W E S N : Complex}
-- given
  (hW : (starRingEnd Complex) W = W)
  (hE : (starRingEnd Complex) E = -E)
  (hS : (starRingEnd Complex) S = Complex.I * S)
  (hN : (starRingEnd Complex) N = -Complex.I * N)
  (hcontour : W - E = Complex.I * (S - N)) :
-- imply
  W + E = S + N := by
-- proof
  apply StatMech.Universality.isingFermionic_horizontal_sum_balance W E S N hW hE hS hN hcontour

/--
[isingFermionic_vertical_sum_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma isingFermionic_vertical_sum_balance_eq
  {W E S N : Complex}
-- given
  (hW : (starRingEnd Complex) W = -Complex.I * W)
  (hE : (starRingEnd Complex) E = Complex.I * E)
  (hS : (starRingEnd Complex) S = S)
  (hN : (starRingEnd Complex) N = -N)
  (hcontour : W - E = Complex.I * (S - N)) :
-- imply
  W + E = S + N := by
-- proof
  apply StatMech.Universality.isingFermionic_vertical_sum_balance W E S N hW hE hS hN hcontour

/--
[isingProj_add_of_complementary_arg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma isingProj_add_of_complementary_arg_eq
  {e x y : Complex}
-- given
  (he : Complex.normSq e = 1)
  (hx : (starRingEnd Complex) x = e * x)
  (hy : (starRingEnd Complex) y = -e * y) :
-- imply
  isingProj e (x + y) = x := by
-- proof
  apply StatMech.Universality.isingProj_add_of_complementary_arg e x y he hx hy

/--
[fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal) :
-- imply
  fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .west)) = 3 ∧ fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .east)) = 7 ∧ fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .south)) = 9 ∧ fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .north)) = 13 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local n hn e haxis

/--
[fkIsingSquareWiredDirectedTangentCode_bond_vertical_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma fkIsingSquareWiredDirectedTangentCode_bond_vertical_local_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical) :
-- imply
  fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .west)) = 5 ∧ fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .east)) = 9 ∧ fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .south)) = 11 ∧ fkIsingSquareWiredDirectedTangentCode n hn (.bond (e, .north)) = 15 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredDirectedTangentCode_bond_vertical_local n hn e haxis

/--
[fkIsingSquareWiredDirectedTangent_horizontal_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma fkIsingSquareWiredDirectedTangent_horizontal_local_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal) :
-- imply
  fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) = 1 ∧ fkIsingSquareWiredDirectedTangent n hn (.dart (e, .east)) = -1 ∧ fkIsingSquareWiredDirectedTangent n hn (.dart (e, .south)) = Complex.I ∧ fkIsingSquareWiredDirectedTangent n hn (.dart (e, .north)) = -Complex.I := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis

/--
[fkIsingSquareWiredDirectedTangent_vertical_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma fkIsingSquareWiredDirectedTangent_vertical_local_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical) :
-- imply
  fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) = -Complex.I ∧ fkIsingSquareWiredDirectedTangent n hn (.dart (e, .east)) = Complex.I ∧ fkIsingSquareWiredDirectedTangent n hn (.dart (e, .south)) = 1 ∧ fkIsingSquareWiredDirectedTangent n hn (.dart (e, .north)) = -1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis

/--
[fkIsingSquareWiredPrimitiveIncrement_local_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma fkIsingSquareWiredPrimitiveIncrement_local_closed_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .west)) + fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .east)) = fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .south)) + fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPrimitiveIncrement_local_closed n hn e

/--
[fkIsingSquareWired_fermionicObservable_opposite_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma fkIsingSquareWired_fermionicObservable_opposite_sum_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (e, .west)) + (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (e, .east)) = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (e, .south)) + (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_fermionicObservable_opposite_sum n hn e

/--
[fkIsingSquareWiredFullMedialObservable_eq_south_add_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma fkIsingSquareWiredFullMedialObservable_eq_south_add_north_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredFullMedialObservable n hn e = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (e, .south)) + (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredFullMedialObservable_eq_south_add_north n hn e

/--
[fkIsingSquareWiredFullMedialObservable_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma fkIsingSquareWiredFullMedialObservable_projection_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n) :
-- imply
  isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (e, s))) (fkIsingSquareWiredFullMedialObservable n hn e) = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (e, s)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredFullMedialObservable_projection n hn e s

/--
[fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, s)) = Complex.normSq (isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (e, s))) (fkIsingSquareWiredFullMedialObservable n hn e)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection n hn e s

/--
[fkIsingSquareWired_normSq_full_eq_west_add_east_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma fkIsingSquareWired_normSq_full_eq_west_add_east_increment_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  Complex.normSq (fkIsingSquareWiredFullMedialObservable n hn e) = fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .west)) + fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .east)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_normSq_full_eq_west_add_east_increment n hn e

/--
[fkIsingSquareWired_normSq_full_eq_south_add_north_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean)
-/
@[path]
private lemma fkIsingSquareWired_normSq_full_eq_south_add_north_increment_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  Complex.normSq (fkIsingSquareWiredFullMedialObservable n hn e) = fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .south)) + fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_normSq_full_eq_south_add_north_increment n hn e


-- created on 2026-10-23
