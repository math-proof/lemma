import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FreeParityErrorReduction.Part3
open Set StatMech StatMech.FK


/--
[clusterMarkCount_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorReduction.lean)
-/
@[path]
private lemma clusterMarkCount_union_eq
  {G : SimpleGraph V}
  {omega : ConfigSpace (Sym2 V)}
  [DecidableEq V]
  {A B : Finset V}
  {C : (openSub G omega).ConnectedComponent}
-- given
  (hdisj : Disjoint A B) :
-- imply
  clusterMarkCount G omega (A ∪ B) C = clusterMarkCount G omega A C + clusterMarkCount G omega B C := by
-- proof
  apply StatMech.FK.clusterMarkCount_union G omega A B hdisj C

/--
[sum_clusterMarkCount_markedComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorReduction.lean)
-/
@[path]
private lemma sum_clusterMarkCount_markedComponents_eq
  {G : SimpleGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {A : Finset V} :
-- imply
  ∑ C ∈ markedComponents G omega A, clusterMarkCount G omega A C = A.card := by
-- proof
  apply StatMech.FK.sum_clusterMarkCount_markedComponents G omega A

/--
[mem_markedComponents_of_odd_clusterMarkCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorReduction.lean)
-/
@[path]
private lemma mem_markedComponents_of_odd_clusterMarkCount_eq
  {G : SimpleGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {A : Finset V}
  {C : (openSub G omega).ConnectedComponent}
-- given
  (hodd : Odd (clusterMarkCount G omega A C)) :
-- imply
  C ∈ markedComponents G omega A := by
-- proof
  apply StatMech.FK.mem_markedComponents_of_odd_clusterMarkCount G omega A C hodd

/--
[allClustersEven_union_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorReduction.lean)
-/
@[path]
private lemma allClustersEven_union_of_disjoint_eq
  {G : SimpleGraph V}
  {omega : ConfigSpace (Sym2 V)}
  [DecidableEq V]
  {A B : Finset V}
-- given
  (hdisj : Disjoint A B)
  (hA : AllClustersEven G omega A)
  (hB : AllClustersEven G omega B) :
-- imply
  AllClustersEven G omega (A ∪ B) := by
-- proof
  apply StatMech.FK.allClustersEven_union_of_disjoint G omega A B hdisj hA hB

/--
[allClustersEven_union_error_subset_twoOddCrossClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorReduction.lean)
-/
@[path]
private lemma allClustersEven_union_error_subset_twoOddCrossClusters_eq
  {G : SimpleGraph V}
  {omega : ConfigSpace (Sym2 V)}
  [DecidableEq V]
  {A B : Finset V}
-- given
  (hdisj : Disjoint A B)
  (hAcard : Even A.card)
  (hBcard : Even B.card)
  (hUnion : AllClustersEven G omega (A ∪ B))
  (herror : ¬ (AllClustersEven G omega A ∧ AllClustersEven G omega B)) :
-- imply
  TwoOddCrossClusters G omega A B := by
-- proof
  apply StatMech.FK.allClustersEven_union_error_subset_twoOddCrossClusters G omega A B hdisj hAcard hBcard hUnion herror

/--
[allClustersEven_factorization_error_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorReduction.lean)
-/
@[path]
private lemma allClustersEven_factorization_error_subset_eq
  {G : SimpleGraph V}
  [DecidableEq V]
  {A B : Finset V}
-- given
  (hdisj : Disjoint A B)
  (hAcard : Even A.card)
  (hBcard : Even B.card) :
-- imply
  allClustersEvenEvent G (A ∪ B) \ (allClustersEvenEvent G A ∩ allClustersEvenEvent G B) ⊆ twoOddCrossClustersEvent G A B := by
-- proof
  apply StatMech.FK.allClustersEven_factorization_error_subset G A B hdisj hAcard hBcard


-- created on 2026-10-23
