import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.LocalRing.ResidueField.AdjoinRootLift
open Polynomial
open DVRResidue


/--
[exists_monic_lift_adjoinRoot_domain](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
private lemma exists_monic_lift_adjoinRoot_domain_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {gbar : (IsLocalRing.ResidueField A)[X]}
-- given
  (hmonic : gbar.Monic)
  (hirr : Irreducible gbar) :
-- imply
  ∃ (g : A[X]) (_ : g.Monic) (_ : IsDomain (AdjoinRoot g))
    (_ : Module.Finite A (AdjoinRoot g)),
    g.map (IsLocalRing.residue A) = gbar := by
-- proof
  apply DVRResidue.exists_monic_lift_adjoinRoot_domain gbar hmonic hirr

/--
[adjoinRootQuotientEquivOfMapEq_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
private lemma adjoinRootQuotientEquivOfMapEq_mk_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing R] [IsLocalRing R]
  {g : R[X]}
  {gbar : (IsLocalRing.ResidueField R)[X]}
  {p : R[X]}
-- given
  (hmap : g.map (IsLocalRing.residue R) = gbar) :
-- imply
  adjoinRootQuotientEquivOfMapEq g gbar hmap
    (Ideal.Quotient.mk _ (AdjoinRoot.mk g p)) =
    AdjoinRoot.mk gbar (p.map (IsLocalRing.residue R)) := by
-- proof
  apply DVRResidue.adjoinRootQuotientEquivOfMapEq_mk g gbar hmap p

/--
[adjoinRoot_map_maximalIdeal_isMaximal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
private lemma adjoinRoot_map_maximalIdeal_isMaximal_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsLocalRing A]
  {g : A[X]}
-- given
  (hirr : Irreducible (g.map (IsLocalRing.residue A))) :
-- imply
  (Ideal.map (algebraMap A (AdjoinRoot g))
    (IsLocalRing.maximalIdeal A)).IsMaximal := by
-- proof
  apply DVRResidue.adjoinRoot_map_maximalIdeal_isMaximal hirr

/--
[adjoinRoot_isLocalRing_of_monic_of_irreducible_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
private lemma adjoinRoot_isLocalRing_of_monic_of_irreducible_map_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsLocalRing A]
  {g : A[X]}
-- given
  (hg : g.Monic)
  (hirr : Irreducible (g.map (IsLocalRing.residue A))) :
-- imply
  IsLocalRing (AdjoinRoot g) := by
-- proof
  apply DVRResidue.adjoinRoot_isLocalRing_of_monic_of_irreducible_map hg hirr

/--
[maximalIdeal_adjoinRoot_eq_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
private lemma maximalIdeal_adjoinRoot_eq_map_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsLocalRing A]
  {g : A[X]} [IsLocalRing (AdjoinRoot g)]
-- given
  (hirr : Irreducible (g.map (IsLocalRing.residue A))) :
-- imply
  IsLocalRing.maximalIdeal (AdjoinRoot g) =
    Ideal.map (AdjoinRoot.of g) (IsLocalRing.maximalIdeal A) := by
-- proof
  apply DVRResidue.maximalIdeal_adjoinRoot_eq_map hirr

/--
[residueFieldEquivAdjoinRootOfMapEq_residue_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
private lemma residueFieldEquivAdjoinRootOfMapEq_residue_mk_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsLocalRing A]
  {g : A[X]} [IsLocalRing (AdjoinRoot g)]
  {gbar : (IsLocalRing.ResidueField A)[X]}
  {p : A[X]}
-- given
  (hirr : Irreducible (g.map (IsLocalRing.residue A)))
  (hmap : g.map (IsLocalRing.residue A) = gbar) :
-- imply
  residueFieldEquivAdjoinRootOfMapEq (g := by
-- proof
  apply DVRResidue.residueFieldEquivAdjoinRootOfMapEq_residue_mk gbar hirr hmap p

/--
[adjoinRoot_isLocalHom_of_irreducible_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
private lemma adjoinRoot_isLocalHom_of_irreducible_map_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsLocalRing A]
  {g : A[X]} [IsLocalRing (AdjoinRoot g)]
-- given
  (hirr : Irreducible (g.map (IsLocalRing.residue A))) :
-- imply
  IsLocalHom (AdjoinRoot.of g) := by
-- proof
  apply DVRResidue.adjoinRoot_isLocalHom_of_irreducible_map hirr

/--
[residueFieldAlgEquivAdjoinRootOfMapEq_residue_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
private lemma residueFieldAlgEquivAdjoinRootOfMapEq_residue_mk_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsLocalRing A]
  {g : A[X]} [IsLocalRing (AdjoinRoot g)] [IsLocalHom (algebraMap A (AdjoinRoot g))]
  {gbar : (IsLocalRing.ResidueField A)[X]}
  {p : A[X]}
-- given
  (hirr : Irreducible (g.map (IsLocalRing.residue A)))
  (hmap : g.map (IsLocalRing.residue A) = gbar) :
-- imply
  residueFieldAlgEquivAdjoinRootOfMapEq (g := by
-- proof
  apply DVRResidue.residueFieldAlgEquivAdjoinRootOfMapEq_residue_mk gbar hirr hmap p

/--
[adjoinRoot_isDiscreteValuationRing_of_monic_of_irreducible_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
private lemma adjoinRoot_isDiscreteValuationRing_of_monic_of_irreducible_map_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {g : A[X]} [IsDomain (AdjoinRoot g)] [IsLocalRing (AdjoinRoot g)]
-- given
  (hg : g.Monic)
  (hirr : Irreducible (g.map (IsLocalRing.residue A))) :
-- imply
  IsDiscreteValuationRing (AdjoinRoot g) := by
-- proof
  apply DVRResidue.adjoinRoot_isDiscreteValuationRing_of_monic_of_irreducible_map hg hirr

/--
[exists_finite_dvr_extension_residueField_algEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
private lemma exists_finite_dvr_extension_residueField_algEquiv_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {A : Type u}
  {L : Type v} [Field L] [Algebra (IsLocalRing.ResidueField A) L] [FiniteDimensional (IsLocalRing.ResidueField A) L] [Algebra.IsSeparable (IsLocalRing.ResidueField A) L] :
-- imply
  ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra A B)
    (_ : Module.Finite A B) (_ : IsDiscreteValuationRing B)
    (_ : IsLocalHom (algebraMap A B)),
    Nonempty (IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A] L) := by
-- proof
  apply DVRResidue.exists_finite_dvr_extension_residueField_algEquiv L


-- created on 2026-10-20
