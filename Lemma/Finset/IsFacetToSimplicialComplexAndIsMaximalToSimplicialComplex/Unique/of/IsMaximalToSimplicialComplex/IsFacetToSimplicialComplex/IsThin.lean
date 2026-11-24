module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
public import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
public import Lemma.Set.ApartmentsToApartmentSystem.eq.Apartments.of.IsThick
public import Lemma.Nat.NotChamberAdjacent
public import Def.v1.Atlas.Buildings.code.Building.AptIsCoxeterProof
public import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex.Part2
open scoped Classical


public section

/--
[thin_unique_other_chamber](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/UniqueLabellingHelper.lean)
-/
@[path]
lemma thin_unique_other_chamber
  {V : Type}
  [DecidableEq V]
  {cc : ChamberComplex V}
  {F C : Finset V}
-- given
  (hthin : cc.IsThin)
  (hFC : cc.toSimplicialComplex.IsFacet F C)
  (hC : cc.toSimplicialComplex.IsMaximal C) :
-- imply
  ∃! D, D ≠ C ∧ cc.toSimplicialComplex.IsFacet F D ∧ cc.toSimplicialComplex.IsMaximal D :=
-- proof
  hthin F C hFC hC
-- In a Coxeter complex, a strictly monotone labelling on faces has
-- $|\text{lab}(s)| = |s|$ for every face $s$.


-- created on 2026-10-24
