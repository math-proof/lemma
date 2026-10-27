import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial IsLocalRing


private noncomputable def J
  {R : Type u} [CommRing R] [IsLocalRing R]
  (f : R[X]) :
  Ideal (AdjoinRoot f) :=
  (maximalIdeal R).map (AdjoinRoot.of f)

private lemma algebraMap_eq_of
  {R : Type u} [CommRing R] [IsLocalRing R]
  (f : R[X]) :
  algebraMap R (AdjoinRoot f) = AdjoinRoot.of f :=
  rfl

private lemma isField_quotient_J
  {R : Type u} [CommRing R] [IsLocalRing R]
  (f : R[X])
  [Fact (Irreducible (f.map (residue R)))] :
  IsField ((AdjoinRoot f) ⧸ (J f)) :=
  MulEquiv.isField (Field.toIsField (AdjoinRoot (f.map (residue R))))
    (AdjoinRoot.quotEquivQuotMap f (maximalIdeal R)).toMulEquiv

private lemma isMaximal_J
  {R : Type u} [CommRing R] [IsLocalRing R]
  (f : R[X])
  [Fact (Irreducible (f.map (residue R)))] :
  (J f).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ (isField_quotient_J f)

private lemma eq_J_of_isMaximal
  {R : Type u} [CommRing R] [IsLocalRing R]
  (f : R[X])
  (hfm : f.Monic)
  [Fact (Irreducible (f.map (residue R)))]
  (N : Ideal (AdjoinRoot f))
  (hN : N.IsMaximal) :
  N = J f := by
  have : Module.Finite R (AdjoinRoot f) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' hfm).basis
  have : Algebra.IsIntegral R (AdjoinRoot f) :=
    Algebra.IsIntegral.of_finite R (AdjoinRoot f)
  have hcomap : (N.comap (algebraMap R (AdjoinRoot f))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap R (AdjoinRoot f)) (fun x => Algebra.IsIntegral.isIntegral x) N
  have hcomap' : N.comap (algebraMap R (AdjoinRoot f)) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal hcomap
  have hle : J f ≤ N := by
    rw [J, ← algebraMap_eq_of, Ideal.map_le_iff_le_comap, hcomap']
  apply Eq.symm
  apply (isMaximal_J f).eq_of_le hN.ne_top hle

private lemma isLocalRing
  {R : Type u} [CommRing R] [IsLocalRing R]
  (f : R[X])
  (hfm : f.Monic)
  [Fact (Irreducible (f.map (residue R)))] :
  IsLocalRing (AdjoinRoot f) :=
  IsLocalRing.of_unique_max_ideal
    ⟨J f, isMaximal_J f, fun N hN => eq_J_of_isMaximal f hfm N hN⟩

private lemma maximalIdeal_eq
  {R : Type u} [CommRing R] [IsLocalRing R]
  (f : R[X])
  (hfm : f.Monic)
  [Fact (Irreducible (f.map (residue R)))] :
  @maximalIdeal (AdjoinRoot f) _ (isLocalRing f hfm) = J f := by
  let _ := isLocalRing f hfm
  apply eq_J_of_isMaximal f hfm _ (IsLocalRing.maximalIdeal.isMaximal _)

private lemma isLocalHom
  {R : Type u} [CommRing R] [IsLocalRing R]
  (f : R[X])
  (hfm : f.Monic)
  [Fact (Irreducible (f.map (residue R)))] :
  IsLocalHom (algebraMap R (AdjoinRoot f)) := by
  let _ := isLocalRing f hfm
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmem : a ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).2 hna
  apply (IsLocalRing.mem_maximalIdeal _).1 _ ha
  ·
    rw [maximalIdeal_eq f hfm]
    apply Ideal.mem_map_of_mem _ hmem

private lemma nonempty_residueField_algEquiv
  {R : Type u} [CommRing R] [IsLocalRing R]
  (f : R[X])
  (hfm : f.Monic)
  [Fact (Irreducible (f.map (residue R)))] :
  letI := isLocalRing f hfm
  letI := isLocalHom f hfm
  Nonempty (AlgEquiv (ResidueField R) (ResidueField (AdjoinRoot f))
    (AdjoinRoot (f.map (residue R)))) := by
  let _ := isLocalRing f hfm
  let _ := isLocalHom f hfm
  let e₁ : ResidueField (AdjoinRoot f) ≃ₐ[R] AdjoinRoot f ⧸ J f :=
    Ideal.quotientEquivAlgOfEq R (maximalIdeal_eq f hfm)
  let e₂ : (AdjoinRoot f ⧸ J f) ≃ₐ[R] AdjoinRoot (f.map (residue R)) :=
    AdjoinRoot.quotEquivQuotMap f (maximalIdeal R)
  let e : ResidueField (AdjoinRoot f) ≃ₐ[R] AdjoinRoot (f.map (residue R)) :=
    e₁.trans e₂
  refine ⟨AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun c => ?_⟩
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
  have h1 : algebraMap (ResidueField R) (ResidueField (AdjoinRoot f)) (residue R r) =
      algebraMap R (ResidueField (AdjoinRoot f)) r := by
    rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  have h2 : algebraMap (ResidueField R) (AdjoinRoot (f.map (residue R))) (residue R r) =
      algebraMap R (AdjoinRoot (f.map (residue R))) r := by
    rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  rw [h1, h2]
  apply e.commutes r

/--
[AdjoinRoot_exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdjoinRoot_exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsLocalRing R]
  {f : R[X]} [Fact (Irreducible (f.map (residue R)))]
-- given
  (hfm : f.Monic) :
-- imply
  ∃ (_ : IsLocalRing (AdjoinRoot f)) (_ : IsLocalHom (algebraMap R (AdjoinRoot f))),
    Module.Finite R (AdjoinRoot f) ∧ Module.Free R (AdjoinRoot f) ∧
      Module.FaithfullyFlat R (AdjoinRoot f) ∧
      Ideal.map (algebraMap R (AdjoinRoot f)) (maximalIdeal R) = maximalIdeal (AdjoinRoot f) ∧
      Nonempty (AlgEquiv (ResidueField R) (ResidueField (AdjoinRoot f))
        (AdjoinRoot (f.map (residue R)))) := by
-- proof
  let hlh := isLocalHom f hfm
  have : IsLocalRing (AdjoinRoot f) := isLocalRing f hfm
  have hfree : Module.Free R (AdjoinRoot f) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hfm).basis
  have hfin : Module.Finite R (AdjoinRoot f) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' hfm).basis
  have hflat : Module.Flat R (AdjoinRoot f) := Module.Flat.of_free
  refine ⟨isLocalRing f hfm, hlh, inferInstance, inferInstance,
    Module.FaithfullyFlat.of_flat_of_isLocalHom, ?_,
    nonempty_residueField_algEquiv f hfm⟩
  rw [algebraMap_eq_of]
  apply Eq.symm
  apply maximalIdeal_eq f hfm


-- created on 2026-10-09
