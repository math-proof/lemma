import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.RingTheory.LocalRing.ResidueField.AdjoinRootLift.Part3
open Polynomial
open DVRResidue


namespace DVRResidue

/--
[exists_monic_lift_adjoinRoot_domain](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
lemma exists_monic_lift_adjoinRoot_domain
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
  have hlift : gbar ∈ Polynomial.lifts (IsLocalRing.residue A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro c
    exact IsLocalRing.residue_surjective (gbar.coeff c)
  obtain ⟨g, hmap, _hdeg, hg⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hmonic
  have hirr_map : Irreducible (g.map (IsLocalRing.residue A)) := hmap ▸ hirr
  have hgirr : Irreducible g :=
    Polynomial.Monic.irreducible_of_irreducible_map (IsLocalRing.residue A) g
      hg hirr_map
  have hprime : Prime g := UniqueFactorizationMonoid.irreducible_iff_prime.mp hgirr
  have hdom : IsDomain (AdjoinRoot g) := AdjoinRoot.isDomain_of_prime hprime
  have hfin : Module.Finite A (AdjoinRoot g) := hg.finite_adjoinRoot
  exact ⟨g, hg, hdom, hfin, hmap⟩

end DVRResidue

namespace DVRResidue

/--
[adjoinRoot_isLocalRing_of_monic_of_irreducible_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
lemma adjoinRoot_isLocalRing_of_monic_of_irreducible_map
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsLocalRing A]
  {g : A[X]}
-- given
  (hg : g.Monic)
  (hirr : Irreducible (g.map (IsLocalRing.residue A))) :
-- imply
  IsLocalRing (AdjoinRoot g) := by
-- proof
  let _ : Module.Finite A (AdjoinRoot g) := hg.finite_adjoinRoot
  let _ : Algebra.IsIntegral A (AdjoinRoot g) :=
    Algebra.IsIntegral.of_finite A (AdjoinRoot g)
  refine IsLocalRing.of_unique_max_ideal ⟨_,
    adjoinRoot_map_maximalIdeal_isMaximal (g := g) hirr, fun M hM => ?_⟩
  let _ : M.IsMaximal := hM
  have hc : (M.comap (algebraMap A (AdjoinRoot g))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap A (AdjoinRoot g))
      (algebraMap_isIntegral_iff.mpr inferInstance) M
  have hle :
    Ideal.map (algebraMap A (AdjoinRoot g)) (IsLocalRing.maximalIdeal A) ≤
      M :=
    IsLocalRing.eq_maximalIdeal hc ▸ Ideal.map_comap_le
  exact ((adjoinRoot_map_maximalIdeal_isMaximal (g := g) hirr).eq_of_le
    hM.ne_top hle).symm

end DVRResidue

namespace DVRResidue

/--
[adjoinRoot_isLocalHom_of_irreducible_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
lemma adjoinRoot_isLocalHom_of_irreducible_map
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsLocalRing A]
  {g : A[X]} [IsLocalRing (AdjoinRoot g)]
-- given
  (hirr : Irreducible (g.map (IsLocalRing.residue A))) :
-- imply
  IsLocalHom (AdjoinRoot.of g) := by
-- proof
  have h := ((IsLocalRing.local_hom_TFAE (AdjoinRoot.of g)).out 4 1).mp
  apply h
  rwa [maximalIdeal_adjoinRoot_eq_map (g := g) hirr]

end DVRResidue

namespace DVRResidue

/--
[residueFieldAlgEquivAdjoinRootOfMapEq_residue_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
lemma residueFieldAlgEquivAdjoinRootOfMapEq_residue_mk
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
  change (residueFieldEquivAdjoinRootOfMapEq (g := g) gbar hirr hmap)
    (IsLocalRing.residue (AdjoinRoot g) (AdjoinRoot.mk g p)) = _
  exact residueFieldEquivAdjoinRootOfMapEq_residue_mk (g := g) gbar hirr hmap p

end DVRResidue

namespace DVRResidue

/--
[adjoinRoot_isDiscreteValuationRing_of_monic_of_irreducible_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
lemma adjoinRoot_isDiscreteValuationRing_of_monic_of_irreducible_map
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {g : A[X]} [IsDomain (AdjoinRoot g)] [IsLocalRing (AdjoinRoot g)]
-- given
  (hg : g.Monic)
  (hirr : Irreducible (g.map (IsLocalRing.residue A))) :
-- imply
  IsDiscreteValuationRing (AdjoinRoot g) := by
-- proof
  let _ : Module.Finite A (AdjoinRoot g) := hg.finite_adjoinRoot
  let _ : IsNoetherianRing (AdjoinRoot g) :=
    IsNoetherianRing.of_finite A (AdjoinRoot g)
  have hdeg : g.degree ≠ 0 := by
    intro hzero
    have hpos := Polynomial.degree_pos_of_irreducible hirr
    have hle : (g.map (IsLocalRing.residue A)).degree ≤ g.degree :=
      Polynomial.degree_map_le
    rw [hzero] at hle
    exact (lt_irrefl _) (hpos.trans_le hle)
  have hinj : Function.Injective (algebraMap A (AdjoinRoot g)) := by
    have h := AdjoinRoot.of.injective_of_degree_ne_zero hdeg
    rwa [← AdjoinRoot.algebraMap_eq] at h
  have hnotfield : ¬IsField (AdjoinRoot g) := by
    intro hfield
    exact IsDiscreteValuationRing.not_isField A
      (isField_of_isIntegral_of_isField hinj hfield)
  have hprincipal : (IsLocalRing.maximalIdeal (AdjoinRoot g)).IsPrincipal := by
    rw [maximalIdeal_adjoinRoot_eq_map (g := g) hirr]
    have hbase : (IsLocalRing.maximalIdeal A).IsPrincipal := inferInstance
    exact hbase.map_ringHom (AdjoinRoot.of g)
  exact ((IsDiscreteValuationRing.TFAE (AdjoinRoot g) hnotfield).out 5 1).mp
    hprincipal
section EssentialSurjectivity
universe u v

end DVRResidue

namespace DVRResidue

/--
[exists_finite_dvr_extension_residueField_algEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean)
-/
@[path]
lemma exists_finite_dvr_extension_residueField_algEquiv
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {A : Type u}
  {L : Type v} [Field L] [Algebra (IsLocalRing.ResidueField A) L] [FiniteDimensional (IsLocalRing.ResidueField A) L] [Algebra.IsSeparable (IsLocalRing.ResidueField A) L] :
-- imply
  ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra A B)
    (_ : Module.Finite A B) (_ : IsDiscreteValuationRing B)
    (_ : IsLocalHom (algebraMap A B)),
    Nonempty (IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A] L) := by
-- proof
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (IsLocalRing.ResidueField A) L
  have hint : IsIntegral (IsLocalRing.ResidueField A) α :=
    (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  obtain ⟨g, hg, hdom, hfin, hmap⟩ := exists_monic_lift_adjoinRoot_domain (A := A)
    (minpoly (IsLocalRing.ResidueField A) α) (minpoly.monic hint)
    (minpoly.irreducible hint)
  have hirr_map : Irreducible (g.map (IsLocalRing.residue A)) :=
    hmap ▸ minpoly.irreducible hint
  let hComm : CommRing (AdjoinRoot g) := inferInstance
  let _ : CommRing (AdjoinRoot g) := hComm
  let hAlg : Algebra A (AdjoinRoot g) := inferInstance
  let _ : Algebra A (AdjoinRoot g) := hAlg
  have hDom : IsDomain (AdjoinRoot g) := hdom
  let _ : IsDomain (AdjoinRoot g) := hDom
  have hFin : Module.Finite A (AdjoinRoot g) := hfin
  let _ : Module.Finite A (AdjoinRoot g) := hFin
  let _ : IsLocalRing (AdjoinRoot g) :=
    adjoinRoot_isLocalRing_of_monic_of_irreducible_map
      (g := g) hg hirr_map
  have hDVR : IsDiscreteValuationRing (AdjoinRoot g) :=
    adjoinRoot_isDiscreteValuationRing_of_monic_of_irreducible_map
      (g := g) hg hirr_map
  let _ : IsDiscreteValuationRing (AdjoinRoot g) := hDVR
  have hLocMap : IsLocalHom (algebraMap A (AdjoinRoot g)) := by
    simpa only [AdjoinRoot.algebraMap_eq] using
      adjoinRoot_isLocalHom_of_irreducible_map (g := g) hirr_map
  let _ : IsLocalHom (algebraMap A (AdjoinRoot g)) := hLocMap
  have hadj : Algebra.adjoin (IsLocalRing.ResidueField A) ({α} : Set L) = ⊤ :=
    Algebra.adjoin_eq_top_of_intermediateField
      (fun _ _ => Algebra.IsAlgebraic.isAlgebraic _) hα
  have e1 : AdjoinRoot (minpoly (IsLocalRing.ResidueField A) α)
    ≃ₐ[IsLocalRing.ResidueField A] L :=
    (minpoly.equivAdjoin hint).trans
      ((Subalgebra.equivOfEq _ _ hadj).trans Subalgebra.topEquiv)
  have e0 : IsLocalRing.ResidueField (AdjoinRoot g)
    ≃ₐ[IsLocalRing.ResidueField A]
    AdjoinRoot (minpoly (IsLocalRing.ResidueField A) α) :=
    residueFieldAlgEquivAdjoinRootOfMapEq (g := g) _ hirr_map hmap
  refine ⟨AdjoinRoot g, hComm, hDom, hAlg, hFin, hDVR, hLocMap, ?_⟩
  exact Nonempty.intro (e0.trans e1)

end DVRResidue

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


-- created on 2026-10-20
-- updated on 2026-10-26
