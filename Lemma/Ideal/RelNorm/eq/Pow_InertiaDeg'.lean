import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false


section Closure

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Module.IsTorsionFree R S]
attribute [instance 10] FractionRing.liftAlgebra
noncomputable instance : Algebra S (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))) := ((algebraMap (FractionRing S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S)))).comp (algebraMap S (FractionRing S))).toAlgebra
noncomputable instance : IsScalarTower S (FractionRing S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))) := IsScalarTower.of_algebraMap_eq' rfl
noncomputable instance : Algebra (Ring.NormalClosure R S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))) := inferInstanceAs (Algebra (integralClosure S (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S)))) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))))
noncomputable instance : IsScalarTower S (Ring.NormalClosure R S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))) := inferInstanceAs (IsScalarTower S (integralClosure S (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S)))) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))))
noncomputable instance : IsIntegralClosure (Ring.NormalClosure R S) S (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))) := integralClosure.isIntegralClosure S (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S)))
noncomputable instance : IsScalarTower R (Ring.NormalClosure R S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))) := by
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  apply Subtype.ext
  show algebraMap R (AlgebraicClosure (FractionRing S)) r =
    algebraMap (FractionRing S) (AlgebraicClosure (FractionRing S)) (algebraMap S (FractionRing S) (algebraMap R S r))
  rw [IsScalarTower.algebraMap_apply R (FractionRing S) (AlgebraicClosure (FractionRing S)), IsScalarTower.algebraMap_apply R S (FractionRing S)]
noncomputable instance : FaithfulSMul S (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))) := (faithfulSMul_iff_algebraMap_injective S (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S)))).mpr <|
      (FaithfulSMul.algebraMap_injective (FractionRing S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S)))).comp (FaithfulSMul.algebraMap_injective S (FractionRing S))
variable [Module.Finite R S]
noncomputable instance : FiniteDimensional (FractionRing S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))) := Module.Finite.right (FractionRing R) (FractionRing S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S)))
noncomputable instance : IsFractionRing (Ring.NormalClosure R S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))) := integralClosure.isFractionRing_of_finite_extension (FractionRing S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S)))
variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
private lemma isSeparable_normalClosure : Algebra.IsSeparable (FractionRing R) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))) := by
  rw [← le_separableClosure_iff, normalClosure_le_iff]
  intro f x hx
  obtain ⟨y, rfl⟩ := f.mem_fieldRange.mp hx
  rw [mem_separableClosure_iff]
  exact IsSeparable.map f (f : (FractionRing S) →+* AlgebraicClosure (FractionRing S)).injective
    (Algebra.IsSeparable.isSeparable (FractionRing R) y)
noncomputable instance : Algebra.IsSeparable (FractionRing R) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))) := isSeparable_normalClosure R S
noncomputable instance : Algebra.IsSeparable (FractionRing S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))) := Algebra.isSeparable_tower_top_of_isSeparable (FractionRing R) (FractionRing S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S)))
noncomputable instance : IsAlgClosure (FractionRing R) (AlgebraicClosure (FractionRing S)) :=
  IsAlgClosure.ofAlgebraic (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))
noncomputable instance : Normal (FractionRing R) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))) := normalClosure.normal _ _ _
noncomputable instance : IsGalois (FractionRing R) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))) := IsGalois.mk
noncomputable instance : IsGalois (FractionRing R) (FractionRing (Ring.NormalClosure R S)) := by
  refine IsGalois.of_equiv_equiv (F := (FractionRing R)) (E := (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))))
    (f := (FractionRing.algEquiv R (FractionRing R)).symm.toRingEquiv)
    (g := (FractionRing.algEquiv (Ring.NormalClosure R S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S)))).symm.toRingEquiv) ?_
  ext
  simpa using IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R (FractionRing R)).symm
    (FractionRing.algEquiv (Ring.NormalClosure R S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S)))).symm _
variable [IsDedekindDomain S]
noncomputable instance : Module.Finite S (Ring.NormalClosure R S) := IsIntegralClosure.finite S (FractionRing S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S))) (Ring.NormalClosure R S)
noncomputable instance : Module.Finite R (Ring.NormalClosure R S) := Module.Finite.trans S (Ring.NormalClosure R S)
noncomputable instance : IsDedekindDomain (Ring.NormalClosure R S) := integralClosure.isDedekindDomain S (FractionRing S) (IntermediateField.normalClosure (FractionRing R) (FractionRing S) (AlgebraicClosure (FractionRing S)))
variable {R S}
variable [IsDedekindDomain R]
private lemma relNorm_eq_pow_of_isMaximal_fractionRing
  (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ P.inertiaDeg R := by
  obtain ⟨Q, hQ₁, hQ₂⟩ : ∃ Q : Ideal (Ring.NormalClosure R S), Q.IsMaximal ∧ Q.LiesOver P :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral P
  have htower : Q.inertiaDeg R = P.inertiaDeg R * Q.inertiaDeg S :=
    Ideal.inertiaDeg_tower (q := P) (r := Q)
  have : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have h := Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
  have : IsGalois (FractionRing S) (FractionRing (Ring.NormalClosure R S)) :=
    IsGalois.tower_top_of_isGalois (FractionRing R) (FractionRing S)
      (FractionRing (Ring.NormalClosure R S))
  rwa [← Ideal.relNorm_relNorm R S, Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    htower, pow_mul, pow_left_inj] at h
  exact Nat.ne_zero_iff_zero_lt.mpr (Ideal.inertiaDeg_pos (q := Q) (R := S))
end Closure
section Transport
variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Module.IsTorsionFree R S] [Module.Finite R S]
  [IsDedekindDomain R] [IsDedekindDomain S]
attribute [instance 10] FractionRing.liftAlgebra
private lemma relNorm_eq_pow_of_isMaximal_of_isSeparable
  (K L : Type*) [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsSeparable K L]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ P.inertiaDeg R := by
  have hsep : Algebra.IsSeparable (FractionRing R) (FractionRing S) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv R K).symm.toRingEquiv
      (FractionRing.algEquiv S L).symm.toRingEquiv ?_
    ext x
    simpa using IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
      (FractionRing.algEquiv S L).symm x
  let _ := hsep
  apply relNorm_eq_pow_of_isMaximal_fractionRing P p

end Transport

/--
[AlgebraicCurve_relNorm_eq_pow_of_isMaximal_of_isSeparable](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_relNorm_eq_pow_of_isMaximal_of_isSeparable.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S]
  [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
  [Algebra.IsSeparable K L]
  {P : Ideal S} {p : Ideal R} [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
-- imply
  Ideal.relNorm R P = p ^ P.inertiaDeg R := by
-- proof
  apply relNorm_eq_pow_of_isMaximal_of_isSeparable K L P p


-- created on 2026-10-20
