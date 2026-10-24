import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectInducedConditionalLower
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectInducedGraph_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectInducedConditionalLower.lean)
-/
@[path]
private lemma fkRectInducedGraph_adjMatch_eq
  {R : FKRectTorus}
  {S : Set R.Vertex} :
-- imply
  FK.ocd_AdjMatch (fkRectInducedGraph R S) (fkRectTorusGraph R) (Subtype.val : FKRectInducedVertex R S → R.Vertex) := by
-- proof
  apply StatMech.FrontierD.fkRectInducedGraph_adjMatch R S

/--
[fkRectFullGraphEvent_mass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectInducedConditionalLower.lean)
-/
@[path]
private lemma fkRectFullGraphEvent_mass_eq_eq
  {R : FKRectTorus}
  {q : Real}
  {B : Set R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  (∑ rho : ConfigSpace (Sym2 R.Vertex), (fkRectFullGraphEvent R B).indicator (fun _ => (1 : Real)) rho * FK.fkProb (fkRectTorusGraph R) (fkRectCriticalP q) q rho) = fkRectCriticalEventMass R q B := by
-- proof
  apply StatMech.FrontierD.fkRectFullGraphEvent_mass_eq R hq B

/--
[fkRectFullGraphEvent_dependsOnOutside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectInducedConditionalLower.lean)
-/
@[path]
private lemma fkRectFullGraphEvent_dependsOnOutside_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {B : Set R.Configuration}
-- given
  (hB : FKRectDependsOnOutsideRegion R S B) :
-- imply
  FK.DependsOnOutside (FK.ocd_innerEdgeFinset (Vin := FKRectInducedVertex R S) (Subtype.val : FKRectInducedVertex R S → R.Vertex)) (fkRectFullGraphEvent R B) := by
-- proof
  apply StatMech.FrontierD.fkRectFullGraphEvent_dependsOnOutside R S hB

/--
[fkRectInduced_freeMass_mul_eventMass_le_genericInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectInducedConditionalLower.lean)
-/
@[path]
private lemma fkRectInduced_freeMass_mul_eventMass_le_genericInter_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {q : Real}
  {A : Set (ConfigSpace (Sym2 (FKRectInducedVertex R S)))}
  {B : Set R.Configuration}
-- given
  (hq : 1 ≤ q)
  (hA : IsIncreasing A)
  (hB : FK.DependsOnOutside (FK.ocd_innerEdgeFinset (Vin := FKRectInducedVertex R S) (Subtype.val : FKRectInducedVertex R S → R.Vertex)) (fkRectFullGraphEvent R B)) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : Real)) omega * FK.fkProb (fkRectInducedGraph R S) (fkRectCriticalP q) q omega) * fkRectCriticalEventMass R q B ≤ ∑ rho, ((FK.ocd_innerRestrict (Subtype.val : FKRectInducedVertex R S → R.Vertex) ⁻¹' A) ∩ fkRectFullGraphEvent R B).indicator (fun _ => (1 : Real)) rho * FK.fkProb (fkRectTorusGraph R) (fkRectCriticalP q) q rho := by
-- proof
  apply StatMech.FrontierD.fkRectInduced_freeMass_mul_eventMass_le_genericInter R S hq hA hB

/--
[fkRectInduced_freeMass_mul_indexedOutsideMass_le_genericInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectInducedConditionalLower.lean)
-/
@[path]
private lemma fkRectInduced_freeMass_mul_indexedOutsideMass_le_genericInter_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {q : Real}
  {A : Set (ConfigSpace (Sym2 (FKRectInducedVertex R S)))}
  {B : Set R.Configuration}
-- given
  (hq : 1 ≤ q)
  (hA : IsIncreasing A)
  (hB : FKRectDependsOnOutsideRegion R S B) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : Real)) omega * FK.fkProb (fkRectInducedGraph R S) (fkRectCriticalP q) q omega) * fkRectCriticalEventMass R q B ≤ ∑ rho, ((FK.ocd_innerRestrict (Subtype.val : FKRectInducedVertex R S → R.Vertex) ⁻¹' A) ∩ fkRectFullGraphEvent R B).indicator (fun _ => (1 : Real)) rho * FK.fkProb (fkRectTorusGraph R) (fkRectCriticalP q) q rho := by
-- proof
  apply StatMech.FrontierD.fkRectInduced_freeMass_mul_indexedOutsideMass_le_genericInter R S hq hA hB


-- created on 2026-10-23
