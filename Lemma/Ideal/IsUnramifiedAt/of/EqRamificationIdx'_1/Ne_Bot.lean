import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing


private noncomputable def quotEquiv
  {R : Type u} [CommRing R] (p : Ideal R) [p.IsMaximal] :
  (R ⧸ p) ≃+* p.ResidueField :=
  RingEquiv.ofBijective (algebraMap (R ⧸ p) p.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField p)

private lemma quotEquiv_mk
  {R : Type u} [CommRing R] (p : Ideal R) [p.IsMaximal] (r : R) :
-- imply
  quotEquiv p (Ideal.Quotient.mk p r) = algebraMap R p.ResidueField r := by
-- proof
  change algebraMap (R ⧸ p) p.ResidueField (algebraMap R (R ⧸ p) r) = _
  rw [← IsScalarTower.algebraMap_apply]


/--
[Algebra_isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable.lean)
-/
@[path]
private lemma main
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [IsDedekindDomain S] [Algebra.EssFiniteType R S]
  {p : Ideal R} [p.IsMaximal]
  {P : Ideal S} [P.IsPrime] [P.LiesOver p]
-- given
  (hP : P ≠ ⊥)
  (he : p.ramificationIdx' P = 1)
  [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
-- imply
  Algebra.IsUnramifiedAt R P := by
-- proof
  let _ := Localization.AtPrime.algebraOfLiesOver p P
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  rw [Algebra.isUnramifiedAt_iff_map_eq R p P]
  refine ⟨?_, (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff hP ?_).mp he⟩
  ·
    let _ : Field (R ⧸ p) := Ideal.Quotient.field p
    let _ : Field (S ⧸ P) := Ideal.Quotient.field P
    refine Algebra.IsSeparable.of_equiv_equiv (A₁ := R ⧸ p) (B₁ := S ⧸ P) (A₂ := p.ResidueField)
      (B₂ := P.ResidueField) (quotEquiv p) (quotEquiv P) ?_
    apply Ideal.Quotient.ringHom_ext
    ext r
    simp only [RingHom.comp_apply]
    change algebraMap p.ResidueField P.ResidueField (quotEquiv p (Ideal.Quotient.mk p r)) =
      quotEquiv P (algebraMap (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk p r))
    rw [quotEquiv_mk]
    have h1 : algebraMap (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk p r) =
        Ideal.Quotient.mk P (algebraMap R S r) := rfl
    rw [h1, quotEquiv_mk, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S]
  ·
    rw [Ideal.map_le_iff_le_comap]
    apply le_of_eq (Ideal.LiesOver.over (p := p) (P := P))


-- created on 2026-10-13
