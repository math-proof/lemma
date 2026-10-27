import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Set.ApartmentsToApartmentSystem.eq.Apartments.of.IsThick
import Lemma.Nat.NotChamberAdjacent
import Def.v1.Atlas.Buildings.code.Building.AptIsCoxeterProof
import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex.Part2
open scoped Classical


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
