import Mathlib
import sympy.Basic

open Polynomial IsLocalRing

/--
[AdjoinRoot_exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdjoinRoot_exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map.lean)
-/

private lemma  algebraMap_eq_of
  {R : Type u}
  [CommRing R]
  [IsLocalRing R]
  (f : R[X])
  : algebraMap R (AdjoinRoot f) = AdjoinRoot.of f := rfl

private lemma  isField_quotient_J
  {R : Type u}
  [CommRing R]
  [IsLocalRing R]
  (f : R[X])
  [Fact (Irreducible (f.map (residue R)))] : IsField (AdjoinRoot f ⧸ J f) := by
  have hK : IsField ((R ⧸ maximalIdeal R)[X] ⧸ Ideal.span {f.map (Ideal.Quotient.mk (maximalIdeal R))}) :=
    Field.toIsField (AdjoinRoot (f.map (residue R)))
  exact MulEquiv.isField hK (AdjoinRoot.quotEquivQuotMap f (maximalIdeal R)).toMulEquiv

private lemma  isMaximal_J
  {R : Type u}
  [CommRing R]
  [IsLocalRing R]
  (f : R[X])
  [Fact (Irreducible (f.map (residue R)))] : (J f).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ (isField_quotient_J f)

private lemma  eq_J_of_isMaximal
    {R : Type u}
    [CommRing R]
    [IsLocalRing R]
    (f : R[X])
    {f}
    (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))]
    (N : Ideal (AdjoinRoot f)) (hN : N.IsMaximal) : N = J f := by
  haveI : Module.Finite R (AdjoinRoot f) := Module.Finite.of_basis (AdjoinRoot.powerBasis' hfm).basis
  haveI : Algebra.IsIntegral R (AdjoinRoot f) := Algebra.IsIntegral.of_finite R (AdjoinRoot f)
  have hcomap : (N.comap (algebraMap R (AdjoinRoot f))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal N
  have hcomap' : N.comap (algebraMap R (AdjoinRoot f)) = maximalIdeal R := IsLocalRing.eq_maximalIdeal hcomap
  have hle : J f ≤ N := by
    rw [J, ← algebraMap_eq_of, Ideal.map_le_iff_le_comap, hcomap']
  exact ((isMaximal_J f).eq_of_le hN.ne_top hle).symm

private lemma  isLocalRing
  {R : Type u}
  [CommRing R]
  [IsLocalRing R]
  (f : R[X])
  {f}
  (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] : IsLocalRing (AdjoinRoot f) :=
  IsLocalRing.of_unique_max_ideal ⟨J f, isMaximal_J f, fun N hN => eq_J_of_isMaximal hfm N hN⟩

private lemma  maximalIdeal_eq
    {R : Type u}
    [CommRing R]
    [IsLocalRing R]
    (f : R[X])
    {f}
    (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] :
    @maximalIdeal (AdjoinRoot f) _ (isLocalRing hfm) = J f :=
  letI := isLocalRing hfm
  eq_J_of_isMaximal hfm _ (IsLocalRing.maximalIdeal.isMaximal _)

private lemma  isLocalHom
    {R : Type u}
    [CommRing R]
    [IsLocalRing R]
    (f : R[X])
    {f}
    (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] :
    IsLocalHom (algebraMap R (AdjoinRoot f)) := by
  letI := isLocalRing hfm
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmem : a ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).2 hna
  have hJmem : algebraMap R (AdjoinRoot f) a ∈ maximalIdeal (AdjoinRoot f) := by
    rw [maximalIdeal_eq hfm]
    exact Ideal.mem_map_of_mem _ hmem
  exact (IsLocalRing.mem_maximalIdeal _).1 hJmem ha

private lemma  nonempty_residueField_algEquiv
    {R : Type u}
    [CommRing R]
    [IsLocalRing R]
    (f : R[X])
    {f}
    (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] :
    letI := isLocalRing hfm
    letI := isLocalHom hfm
    Nonempty (ResidueField (AdjoinRoot f) ≃ₐ[ResidueField R] AdjoinRoot (f.map (residue R))) := by
  letI := isLocalRing hfm
  letI := isLocalHom hfm

  let e₁ : ResidueField (AdjoinRoot f) ≃ₐ[R] AdjoinRoot f ⧸ J f :=
    Ideal.quotientEquivAlgOfEq R (maximalIdeal_eq hfm)
  let e₂ : (AdjoinRoot f ⧸ J f) ≃ₐ[R] AdjoinRoot (f.map (residue R)) :=
    AdjoinRoot.quotEquivQuotMap f (maximalIdeal R)
  let e : ResidueField (AdjoinRoot f) ≃ₐ[R] AdjoinRoot (f.map (residue R)) := e₁.trans e₂

  refine ⟨AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun c => ?_⟩
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
  have h1 : algebraMap (ResidueField R) (ResidueField (AdjoinRoot f)) (residue R r) =
      algebraMap R (ResidueField (AdjoinRoot f)) r := by
    rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  have h2 : algebraMap (ResidueField R) (AdjoinRoot (f.map (residue R))) (residue R r) =
      algebraMap R (AdjoinRoot (f.map (residue R))) r := by
    rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  rw [h1, h2]
  exact e.commutes r


open P2mAdjoinRootLocalStep in
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsLocalRing R]
  {f : R[X]} [Fact (Irreducible (f.map (residue R)))]
-- given
  (hfm : f.Monic) :
-- imply
  ∃ (_ : IsLocalRing (AdjoinRoot f)) (_ : IsLocalHom (algebraMap R (AdjoinRoot f))),
      Module.Finite R (AdjoinRoot f) ∧ Module.Free R (AdjoinRoot f) ∧ Module.FaithfullyFlat R (AdjoinRoot f) ∧
      Ideal.map (algebraMap R (AdjoinRoot f)) (maximalIdeal R) = maximalIdeal (AdjoinRoot f) ∧
      Nonempty (ResidueField (AdjoinRoot f) ≃ₐ[ResidueField R] AdjoinRoot (f.map (residue R))) := by
-- proof
  letI hloc := isLocalRing hfm
  letI hlh := isLocalHom hfm
  haveI : Module.Free R (AdjoinRoot f) := Module.Free.of_basis (AdjoinRoot.powerBasis' hfm).basis
  haveI : Module.Finite R (AdjoinRoot f) := Module.Finite.of_basis (AdjoinRoot.powerBasis' hfm).basis
  haveI : Module.Flat R (AdjoinRoot f) := Module.Flat.of_free
  refine ⟨hloc, hlh, inferInstance, inferInstance, Module.FaithfullyFlat.of_flat_of_isLocalHom, ?_,
    nonempty_residueField_algEquiv hfm⟩
  rw [algebraMap_eq_of]
  exact (maximalIdeal_eq hfm).symm


-- created on 2026-10-09
