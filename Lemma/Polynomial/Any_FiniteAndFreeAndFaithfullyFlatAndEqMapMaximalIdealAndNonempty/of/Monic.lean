import Mathlib
import sympy.Basic

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
  MulEquiv.isField (Field.toIsField (AdjoinRoot (f.map (residue R)))) (AdjoinRoot.quotEquivQuotMap f (maximalIdeal R)).toMulEquiv

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
  N = J f := sorry















private lemma isLocalRing
  {R : Type u} [CommRing R] [IsLocalRing R]


  (f : R[X])
  (hfm : f.Monic)
  [Fact (Irreducible (f.map (residue R)))] :
  IsLocalRing (AdjoinRoot f) :=
  IsLocalRing.of_unique_max_ideal ⟨J f, isMaximal_J f, fun N hN => eq_J_of_isMaximal f hfm N hN⟩

private lemma maximalIdeal_eq
  {R : Type u} [CommRing R] [IsLocalRing R]


  (f : R[X])
  (hfm : f.Monic)
  [Fact (Irreducible (f.map (residue R)))] :
  @maximalIdeal (AdjoinRoot f) _ (isLocalRing f hfm) = J f := by
  sorry

private lemma isLocalHom
  {R : Type u} [CommRing R] [IsLocalRing R]


  (f : R[X])
  (hfm : f.Monic)
  [Fact (Irreducible (f.map (residue R)))] :
  IsLocalHom (algebraMap R (AdjoinRoot f)) := by sorry








private lemma nonempty_residueField_algEquiv
  {R : Type u} [CommRing R] [IsLocalRing R]


  (f : R[X])
  (hfm : f.Monic)
  [Fact (Irreducible (f.map (residue R)))] :
  letI := isLocalRing f hfm
  letI := isLocalHom f hfm
  Nonempty (AlgEquiv (ResidueField R) (ResidueField (AdjoinRoot f))
    (AdjoinRoot (f.map (residue R)))) := sorry


















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
  haveI : IsLocalRing (AdjoinRoot f) := isLocalRing f hfm
  have hfree : Module.Free R (AdjoinRoot f) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hfm).basis
  have hfin : Module.Finite R (AdjoinRoot f) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' hfm).basis
  have hflat : Module.Flat R (AdjoinRoot f) := Module.Flat.of_free
  refine ⟨isLocalRing f hfm, hlh, inferInstance, inferInstance, Module.FaithfullyFlat.of_flat_of_isLocalHom, ?_,
    nonempty_residueField_algEquiv f hfm⟩
  rw [algebraMap_eq_of]
  exact (maximalIdeal_eq f hfm).symm

-- created on 2026-10-09
