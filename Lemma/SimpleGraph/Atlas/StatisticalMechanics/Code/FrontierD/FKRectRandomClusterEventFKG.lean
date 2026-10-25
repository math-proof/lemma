import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
open StatMech StatMech.FrontierD


/--
[fkRectCriticalEventMass_eq_indicatorExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_eq_indicatorExpectation_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration} :
-- imply
  fkRectCriticalEventMass R q A = ∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * A.indicator (fun _ => (1 : Real)) omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_eq_indicatorExpectation R q A

/--
[fkRectCriticalEventMass_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_univ_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalEventMass R q Set.univ = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_univ R hq

/--
[fkRectCriticalEventMass_compl_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_compl_add_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalEventMass R q Aᶜ + fkRectCriticalEventMass R q A = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_compl_add R hq A

/--
[fkRectCriticalEventMass_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_compl_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalEventMass R q Aᶜ = 1 - fkRectCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_compl R hq A

/--
[fkRectCriticalEventMass_mul_le_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_mul_le_inter_eq
  {R : FKRectTorus}
  {q : Real}
  {A B : Set R.Configuration}
-- given
  (hq : 1 ≤ q)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  fkRectCriticalEventMass R q A * fkRectCriticalEventMass R q B ≤ fkRectCriticalEventMass R q (A ∩ B) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_mul_le_inter R hq hA hB

/--
[fkRectCriticalEventMass_mul_le_inter_decreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_mul_le_inter_decreasing_eq
  {R : FKRectTorus}
  {q : Real}
  {A B : Set R.Configuration}
-- given
  (hq : 1 ≤ q)
  (hA : IsDecreasing A)
  (hB : IsDecreasing B) :
-- imply
  fkRectCriticalEventMass R q A * fkRectCriticalEventMass R q B ≤ fkRectCriticalEventMass R q (A ∩ B) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_mul_le_inter_decreasing R hq hA hB

/--
[fkRectFiniteEventIntersection_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectFiniteEventIntersection_isIncreasing_eq
  {R : FKRectTorus}
  {s : Finset ι}
  {A : ι → Set R.Configuration}
-- given
  (hA : ∀ i ∈ s, IsIncreasing (A i)) :
-- imply
  IsIncreasing (fkRectFiniteEventIntersection s A) := by
-- proof
  apply StatMech.FrontierD.fkRectFiniteEventIntersection_isIncreasing s A hA

/--
[fkRectFiniteEventIntersection_isDecreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectFiniteEventIntersection_isDecreasing_eq
  {R : FKRectTorus}
  {s : Finset ι}
  {A : ι → Set R.Configuration}
-- given
  (hA : ∀ i ∈ s, IsDecreasing (A i)) :
-- imply
  IsDecreasing (fkRectFiniteEventIntersection s A) := by
-- proof
  apply StatMech.FrontierD.fkRectFiniteEventIntersection_isDecreasing s A hA

/--
[fkRectCriticalEventMass_prod_le_finiteIntersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_prod_le_finiteIntersection_eq
  {R : FKRectTorus}
  {q : Real}
  {s : Finset ι}
  {A : ι → Set R.Configuration}
-- given
  (hq : 1 ≤ q)
  (hA : ∀ i ∈ s, IsIncreasing (A i)) :
-- imply
  (∏ i ∈ s, fkRectCriticalEventMass R q (A i)) ≤ fkRectCriticalEventMass R q (fkRectFiniteEventIntersection s A) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_prod_le_finiteIntersection R hq s A hA

/--
[fkRectCriticalEventMass_prod_le_finiteIntersection_decreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_prod_le_finiteIntersection_decreasing_eq
  {R : FKRectTorus}
  {q : Real}
  {s : Finset ι}
  {A : ι → Set R.Configuration}
-- given
  (hq : 1 ≤ q)
  (hA : ∀ i ∈ s, IsDecreasing (A i)) :
-- imply
  (∏ i ∈ s, fkRectCriticalEventMass R q (A i)) ≤ fkRectCriticalEventMass R q (fkRectFiniteEventIntersection s A) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_prod_le_finiteIntersection_decreasing R hq s A hA

/--
[fkRectTorusConnectionEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectTorusConnectionEvent_isIncreasing_eq
  {R : FKRectTorus}
  {x y : R.Vertex} :
-- imply
  IsIncreasing (fkRectTorusConnectionEvent R x y) := by
-- proof
  apply StatMech.FrontierD.fkRectTorusConnectionEvent_isIncreasing R x y

/--
[fkRectTorusConnectionChainEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectTorusConnectionChainEvent_isIncreasing_eq
  {R : FKRectTorus}
  {s : Finset (R.Vertex × R.Vertex)} :
-- imply
  IsIncreasing (fkRectTorusConnectionChainEvent R s) := by
-- proof
  apply StatMech.FrontierD.fkRectTorusConnectionChainEvent_isIncreasing R s

/--
[fkRectCriticalEventMass_connectionChain_ge_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_connectionChain_ge_prod_eq
  {R : FKRectTorus}
  {q : Real}
  {s : Finset (R.Vertex × R.Vertex)}
-- given
  (hq : 1 ≤ q) :
-- imply
  (∏ p ∈ s, fkRectCriticalEventMass R q (fkRectTorusConnectionEvent R p.1 p.2)) ≤ fkRectCriticalEventMass R q (fkRectTorusConnectionChainEvent R s) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_connectionChain_ge_prod R hq s

/--
[fkRectCriticalEventMass_connectionChain_ge_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_connectionChain_ge_pow_eq
  {R : FKRectTorus}
  {q a : Real}
  {s : Finset (R.Vertex × R.Vertex)}
-- given
  (hq : 1 ≤ q)
  (ha : 0 ≤ a)
  (hblock : ∀ p ∈ s, a ≤ fkRectCriticalEventMass R q (fkRectTorusConnectionEvent R p.1 p.2)) :
-- imply
  a ^ s.card ≤ fkRectCriticalEventMass R q (fkRectTorusConnectionChainEvent R s) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_connectionChain_ge_pow R hq ha s hblock

/--
[fkRectCriticalEventMass_event_mul_connectionChain_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_event_mul_connectionChain_le_eq
  {R : FKRectTorus}
  {q : Real}
  {B : Set R.Configuration}
  {s : Finset (R.Vertex × R.Vertex)}
-- given
  (hq : 1 ≤ q)
  (hB : IsIncreasing B) :
-- imply
  fkRectCriticalEventMass R q B * (∏ p ∈ s, fkRectCriticalEventMass R q (fkRectTorusConnectionEvent R p.1 p.2)) ≤ fkRectCriticalEventMass R q (B ∩ fkRectTorusConnectionChainEvent R s) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_event_mul_connectionChain_le R hq B hB s

/--
[fkRectCriticalEventMass_event_mul_pow_le_connectionChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_event_mul_pow_le_connectionChain_eq
  {R : FKRectTorus}
  {q a : Real}
  {B : Set R.Configuration}
  {s : Finset (R.Vertex × R.Vertex)}
-- given
  (hq : 1 ≤ q)
  (ha : 0 ≤ a)
  (hB : IsIncreasing B)
  (hblock : ∀ p ∈ s, a ≤ fkRectCriticalEventMass R q (fkRectTorusConnectionEvent R p.1 p.2)) :
-- imply
  fkRectCriticalEventMass R q B * a ^ s.card ≤ fkRectCriticalEventMass R q (B ∩ fkRectTorusConnectionChainEvent R s) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_event_mul_pow_le_connectionChain R hq ha B hB s hblock

/--
[fkRectCriticalEventMass_finiteUnion_le_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_finiteUnion_le_sum_eq
  {R : FKRectTorus}
  {q : Real}
  {s : Finset ι}
  {A : ι → Set R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalEventMass R q (fkRectFiniteEventUnion s A) ≤ ∑ i ∈ s, fkRectCriticalEventMass R q (A i) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_finiteUnion_le_sum R hq s A

/--
[fkRectCriticalEventMass_union_le_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_union_le_add_eq
  {R : FKRectTorus}
  {q : Real}
  {A B : Set R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalEventMass R q (A ∪ B) ≤ fkRectCriticalEventMass R q A + fkRectCriticalEventMass R q B := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_union_le_add R hq A B

/--
[exists_card_mul_eventMass_ge_of_finiteUnion_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean)
-/
@[path]
private lemma exists_card_mul_eventMass_ge_of_finiteUnion_ge_eq
  {R : FKRectTorus}
  {q c : Real}
  {s : Finset ι}
  {A : ι → Set R.Configuration}
-- given
  (hq : 0 < q)
  (hs : s.Nonempty)
  (hc : c ≤ fkRectCriticalEventMass R q (fkRectFiniteEventUnion s A)) :
-- imply
  ∃ i ∈ s, c ≤ (s.card : Real) * fkRectCriticalEventMass R q (A i) := by
-- proof
  apply StatMech.FrontierD.exists_card_mul_eventMass_ge_of_finiteUnion_ge R hq hs A hc


-- created on 2026-10-23
