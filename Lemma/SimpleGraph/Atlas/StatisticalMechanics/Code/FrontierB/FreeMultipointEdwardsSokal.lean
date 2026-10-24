import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.FreeMultipointEdwardsSokal
open StatMech StatMech.FK


/--
[esSpinProduct_constOnOpenEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeMultipointEdwardsSokal.lean)
-/
@[path]
private lemma esSpinProduct_constOnOpenEquiv_eq
  [Fintype V]
  [DecidableEq V]
  {omega : ConfigSpace (Sym2 V)}
  {A : Finset V}
-- given
  (tau : (openSub G omega).ConnectedComponent -> Fin 2) :
-- imply
  esSpinProduct A ((constOnOpenEquiv G omega tau).1) = ∏ C : (openSub G omega).ConnectedComponent, isingSpin (tau C) ^ clusterMarkCount G omega A C := by
-- proof
  apply StatMech.FK.esSpinProduct_constOnOpenEquiv omega A tau

/--
[sum_isingSpin_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeMultipointEdwardsSokal.lean)
-/
@[path]
private lemma sum_isingSpin_pow_eq
  [Fintype V]
  [DecidableEq V]
  {n : Nat} :
-- imply
  (∑ a : Fin 2, isingSpin a ^ n) = if Even n then 2 else 0 := by
-- proof
  apply StatMech.FK.sum_isingSpin_pow n

/--
[clusterColor_spinProduct_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeMultipointEdwardsSokal.lean)
-/
@[path]
private lemma clusterColor_spinProduct_sum_eq
  [Fintype V]
  [DecidableEq V]
  {omega : ConfigSpace (Sym2 V)}
  {A : Finset V} :
-- imply
  (∑ tau : (openSub G omega).ConnectedComponent -> Fin 2, esSpinProduct A ((constOnOpenEquiv G omega tau).1)) = if AllClustersEven G omega A then 2 ^ numClusters G omega else 0 := by
-- proof
  apply StatMech.FK.clusterColor_spinProduct_sum omega A

/--
[compatible_esSpinProduct_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeMultipointEdwardsSokal.lean)
-/
@[path]
private lemma compatible_esSpinProduct_sum_eq
  [Fintype V]
  [DecidableEq V]
  {omega : ConfigSpace (Sym2 V)}
  {A : Finset V} :
-- imply
  (∑ sigma : V -> Fin 2, (if ConstOnOpen G omega sigma then (1 : Real) else 0) * esSpinProduct A sigma) = if AllClustersEven G omega A then 2 ^ numClusters G omega else 0 := by
-- proof
  apply StatMech.FK.compatible_esSpinProduct_sum omega A

/--
[esWeight_multipoint_spin_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeMultipointEdwardsSokal.lean)
-/
@[path]
private lemma esWeight_multipoint_spin_sum_eq
  [Fintype V]
  [DecidableEq V]
  {p : Real}
  {omega : ConfigSpace (Sym2 V)}
  {A : Finset V} :
-- imply
  (∑ sigma : V -> Fin 2, esWeight G p sigma omega * esSpinProduct A sigma) = if AllClustersEven G omega A then fkWeight G p (2 : Real) omega else 0 := by
-- proof
  apply StatMech.FK.esWeight_multipoint_spin_sum p omega A

/--
[esMultiPoint_eq_allClustersEvenProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeMultipointEdwardsSokal.lean)
-/
@[path]
private lemma esMultiPoint_eq_allClustersEvenProb_eq
  [Fintype V]
  [DecidableEq V]
  {p : Real}
  {A : Finset V} :
-- imply
  esMultiPoint G p A = allClustersEvenProb G p A := by
-- proof
  apply StatMech.FK.esMultiPoint_eq_allClustersEvenProb p A

/--
[isingSpin_eq_neg_spin_toIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeMultipointEdwardsSokal.lean)
-/
@[path]
private lemma isingSpin_eq_neg_spin_toIsing_eq
  [Fintype V]
  [DecidableEq V]
  {x : V}
-- given
  (sigma : V -> Fin 2) :
-- imply
  isingSpin (sigma x) = -Ising.spin (IsingFK.toIsing sigma) x := by
-- proof
  apply StatMech.FK.isingSpin_eq_neg_spin_toIsing sigma x

/--
[esSpinProduct_eq_negOnePow_mul_spinProd_toIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeMultipointEdwardsSokal.lean)
-/
@[path]
private lemma esSpinProduct_eq_negOnePow_mul_spinProd_toIsing_eq
  [Fintype V]
  [DecidableEq V]
  {A : Finset V}
-- given
  (sigma : V -> Fin 2) :
-- imply
  esSpinProduct A sigma = (-1 : Real) ^ A.card * Ising.spinProd A (IsingFK.toIsing sigma) := by
-- proof
  apply StatMech.FK.esSpinProduct_eq_negOnePow_mul_spinProd_toIsing A sigma

/--
[esSpinProduct_eq_spinProd_toIsing_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeMultipointEdwardsSokal.lean)
-/
@[path]
private lemma esSpinProduct_eq_spinProd_toIsing_of_even_eq
  [Fintype V]
  [DecidableEq V]
  {A : Finset V}
-- given
  (hA : Even A.card)
  (sigma : V -> Fin 2) :
-- imply
  esSpinProduct A sigma = Ising.spinProd A (IsingFK.toIsing sigma) := by
-- proof
  apply StatMech.FK.esSpinProduct_eq_spinProd_toIsing_of_even A hA sigma

/--
[esMultiPoint_eq_firstMarginal_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeMultipointEdwardsSokal.lean)
-/
@[path]
private lemma esMultiPoint_eq_firstMarginal_sum_eq
  [Fintype V]
  [DecidableEq V]
  {p : Real}
  {A : Finset V} :
-- imply
  esMultiPoint G p A = ∑ sigma : V -> Fin 2, esFirstMarginal G 2 p sigma * esSpinProduct A sigma := by
-- proof
  apply StatMech.FK.esMultiPoint_eq_firstMarginal_sum p A

/--
[isingExpectation_spinProd_eq_allClustersEvenProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeMultipointEdwardsSokal.lean)
-/
@[path]
private lemma isingExpectation_spinProd_eq_allClustersEvenProb_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {A : Finset V}
-- given
  (hA : Even A.card) :
-- imply
  Ising.isingExpectation G beta 0 (Ising.spinProd A) = allClustersEvenProb G (1 - Real.exp (-2 * beta)) A := by
-- proof
  apply StatMech.FK.isingExpectation_spinProd_eq_allClustersEvenProb beta A hA


-- created on 2026-10-23
