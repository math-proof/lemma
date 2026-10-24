import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Foundations.FiniteBidegreeHall
open Finset


/--
[finiteRelationHall_of_bidegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteBidegreeHall.lean)
-/
@[path]
private lemma finiteRelationHall_of_bidegree_eq
  [Fintype Source]
  [Fintype Target]
  [DecidableRel related]
  {degree : Nat}
-- given
  (related : Source -> Target -> Prop)
  (hdegree : 0 < degree)
  (hsource : forall source, degree <= (Finset.univ.filter (related source)).card)
  (htarget : forall target, (Finset.univ.filter fun source => related source target).card <= degree) :
-- imply
  forall sources : Finset Source, sources.card <= (Finset.univ.filter fun target => ∃ source ∈ sources, related source target).card := by
-- proof
  apply finiteRelationHall_of_bidegree related degree hdegree hsource htarget

/--
[finiteRelationHall_of_certificateEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteBidegreeHall.lean)
-/
@[path]
private lemma finiteRelationHall_of_certificateEmbeddings_eq
  [Finite Source]
  [Fintype Target]
  [DecidableRel related]
  {degree : Nat}
  {sourceCertificates : forall source, Fin degree ↪ {target : Target // related source target}}
  {targetCertificateCode : forall target, {source : Source // related source target} ↪ Fin degree}
-- given
  (related : Source -> Target -> Prop)
  (hdegree : 0 < degree) :
-- imply
  forall sources : Finset Source, sources.card <= (Finset.univ.filter fun target => ∃ source ∈ sources, related source target).card := by
-- proof
  apply finiteRelationHall_of_certificateEmbeddings related degree hdegree sourceCertificates targetCertificateCode

/--
[finiteRelation_exists_injective_of_certificateEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteBidegreeHall.lean)
-/
@[path]
private lemma finiteRelation_exists_injective_of_certificateEmbeddings_eq
  [Finite Source]
  [Finite Target]
  {degree : Nat}
  {sourceCertificates : forall source, Fin degree ↪ {target : Target // related source target}}
  {targetCertificateCode : forall target, {source : Source // related source target} ↪ Fin degree}
-- given
  (related : Source -> Target -> Prop)
  (hdegree : 0 < degree) :
-- imply
  exists matching : Source -> Target, Function.Injective matching ∧ forall source, related source (matching source) := by
-- proof
  apply finiteRelation_exists_injective_of_certificateEmbeddings related degree hdegree sourceCertificates targetCertificateCode


-- created on 2026-10-23
