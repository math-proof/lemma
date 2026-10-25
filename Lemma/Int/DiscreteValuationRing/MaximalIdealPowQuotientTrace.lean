import Mathlib
import sympy.Basic
import Theorem.RingTheory.DiscreteValuationRing.MaximalIdealPowQuotientTrace
open IsLocalRing


/--
[trace_residueFieldMaximalIdealPowQuotient_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowQuotientTrace.lean)
-/
@[path]
lemma trace_residueFieldMaximalIdealPowQuotient_succ
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
  {n : ℕ} [Module (ResidueField A) (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)] [IsScalarTower (ResidueField A) (ResidueField B) (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)] [FiniteDimensional (ResidueField A) (ResidueFieldMaximalIdealPowQuotient A B (n + 1))]
  {b : B}
-- given
  (hSucc : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ (n + 1)) :
-- imply
  Algebra.trace (ResidueField A)
    (ResidueFieldMaximalIdealPowQuotient A B (n + 1))
    (Ideal.Quotient.mk _ b) =
    Algebra.trace (ResidueField A) (ResidueField B)
    (IsLocalRing.residue B b) +
    Algebra.trace (ResidueField A)
    (ResidueFieldMaximalIdealPowQuotient A B n)
    (Ideal.Quotient.mk _ b) := by
-- proof
  have hsurj : Function.Surjective
    (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap :=
    factorResidueFieldMaximalIdealPowQuotient_surjective A B n
  have hcomm :
    (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap.comp
      (Algebra.lmul (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B (n + 1))
        (Ideal.Quotient.mk _ b)) =
    (Algebra.lmul (ResidueField A)
      (ResidueFieldMaximalIdealPowQuotient A B n)
      (Ideal.Quotient.mk _ b)).comp
      (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap := by
    apply LinearMap.ext
    intro x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [LinearMap.comp_apply, Algebra.coe_lmul_eq_mul,
      LinearMap.mul_apply', AlgHom.toLinearMap_apply, ← map_mul,
      factorResidueFieldMaximalIdealPowQuotient_mk]
  have htrace :=
    LinearMap.trace_eq_trace_restrict_ker_add_of_surjective
      (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap
      (Algebra.lmul (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B (n + 1))
        (Ideal.Quotient.mk _ b))
      (Algebra.lmul (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B n)
        (Ideal.Quotient.mk _ b))
      hsurj hcomm
  have hker : ∀ hi : LinearMap.ker
    (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap ≤
    (LinearMap.ker
      (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap).comap
      (Algebra.lmul (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B (n + 1))
        (Ideal.Quotient.mk _ b)),
    LinearMap.trace (ResidueField A)
      (LinearMap.ker
        (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap)
      ((Algebra.lmul (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B (n + 1))
        (Ideal.Quotient.mk _ b)).restrict hi) =
      Algebra.trace (ResidueField A) (ResidueField B)
        (IsLocalRing.residue B b) := by
    intro hi
    have hbridge :
      (residueFieldLinearEquivMaximalIdealGradedPieceKerFactor A B n
        hSucc).conj
        ((IsDiscreteValuationRing.residueFieldMulMaximalIdealGradedPiece B
          (IsLocalRing.residue B b) n).restrictScalars
          (ResidueField A)) =
      (Algebra.lmul (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B (n + 1))
        (Ideal.Quotient.mk _ b)).restrict hi := by
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ :=
        (residueFieldLinearEquivMaximalIdealGradedPieceKerFactor A B n
          hSucc).surjective x
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      apply Subtype.ext
      simp only [LinearEquiv.conj_apply_apply,
        LinearEquiv.symm_apply_apply, LinearMap.restrictScalars_apply,
        IsDiscreteValuationRing.residueFieldMulMaximalIdealGradedPiece_residue_mk,
        residueFieldLinearEquivMaximalIdealGradedPieceKerFactor_mk,
        LinearMap.restrict_apply, Algebra.coe_lmul_eq_mul,
        LinearMap.mul_apply', Submodule.coe_smul, smul_eq_mul, ← map_mul]
    rw [← hbridge, LinearMap.trace_conj',
      IsDiscreteValuationRing.trace_residueFieldMulMaximalIdealGradedPiece]
  simp only [Algebra.trace_apply] at htrace hker ⊢
  rw [htrace, hker]

/--
[trace_residueFieldMaximalIdealPowQuotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowQuotientTrace.lean)
-/
@[path]
lemma trace_residueFieldMaximalIdealPowQuotient
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
  {n : ℕ} [FiniteDimensional (ResidueField A) (ResidueFieldMaximalIdealPowQuotient A B n)]
  {b : B}
-- given
  (h : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ n) :
-- imply
  Algebra.trace (ResidueField A)
    (ResidueFieldMaximalIdealPowQuotient A B n)
    (Ideal.Quotient.mk _ b) =
    n • Algebra.trace (ResidueField A) (ResidueField B)
    (IsLocalRing.residue B b) := by
-- proof
  have key : ∀ (m : ℕ) (_ : Ideal.map (algebraMap A B) (maximalIdeal A) ≤
    maximalIdeal B ^ m)
    [FiniteDimensional (ResidueField A)
      (ResidueFieldMaximalIdealPowQuotient A B m)] (c : B),
    Algebra.trace (ResidueField A)
      (ResidueFieldMaximalIdealPowQuotient A B m)
      (Ideal.Quotient.mk _ c) =
      m • Algebra.trace (ResidueField A) (ResidueField B)
        (IsLocalRing.residue B c) := by
    intro m
    induction m with
    | zero =>
      intro _ _ c
      have htop : (Ideal.map (algebraMap A B) (maximalIdeal A) ⊔
        maximalIdeal B ^ 0 : Ideal B) = ⊤ := by simp
      have hmk : (Ideal.Quotient.mk _ c :
        ResidueFieldMaximalIdealPowQuotient A B 0) = 0 := by
        rwa [Ideal.Quotient.eq_zero_iff_mem, htop]
      simp [hmk]
    | succ m ih =>
      intro hm hfd c
      have hLow : Ideal.map (algebraMap A B) (maximalIdeal A) ≤
        maximalIdeal B ^ m :=
        le_trans hm (Ideal.pow_le_pow_right m.le_succ)
      have hfdL : FiniteDimensional (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B m) :=
        FiniteDimensional.of_surjective
          (factorResidueFieldMaximalIdealPowQuotient A B m).toLinearMap
          (factorResidueFieldMaximalIdealPowQuotient_surjective A B m)
      let hmod : Module (ResidueField A)
        (IsDiscreteValuationRing.MaximalIdealGradedPiece B m) :=
        Module.compHom _ (algebraMap (ResidueField A) (ResidueField B))
      have htower : IsScalarTower (ResidueField A) (ResidueField B)
        (IsDiscreteValuationRing.MaximalIdealGradedPiece B m) :=
        IsScalarTower.of_compHom (ResidueField A) (ResidueField B)
          (IsDiscreteValuationRing.MaximalIdealGradedPiece B m)
      rw [trace_residueFieldMaximalIdealPowQuotient_succ A B m hm c, ih hLow c,
        add_smul, one_smul, add_comm _ _]
  exact key n h b

/--
[residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowQuotientTrace.lean)
-/
@[path]
lemma residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B]
  {e : ℕ}
  {b : B}
-- given
  (he : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ e) :
-- imply
  residue A (Algebra.intTrace A B b) =
    e • Algebra.trace (ResidueField A)
    (ResidueField B) (residue B b) := by
-- proof
  have hle : Ideal.map (algebraMap A B) (maximalIdeal A) ≤
    maximalIdeal B ^ e := he ▸ le_rfl
  have hI : (Ideal.map (algebraMap A B) (maximalIdeal A) ⊔ maximalIdeal B ^ e :
    Ideal B) = Ideal.map (algebraMap A B) (maximalIdeal A) := by
    rw [he, sup_idem]
  have hMathlib := Algebra.trace_quotient_eq_of_isDedekindDomain (R := A) (S := B)
    (p := maximalIdeal A) (x := b)
  let : IsScalarTower A (ResidueField A)
    (ResidueFieldMaximalIdealPowQuotient A B e) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite (ResidueField A)
    (ResidueFieldMaximalIdealPowQuotient A B e) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have hIter := trace_residueFieldMaximalIdealPowQuotient A B e hle b
  let : Algebra (ResidueField A)
    (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) :=
    inferInstanceAs (Algebra (A ⧸ maximalIdeal A) _)
  let e₂ : ResidueFieldMaximalIdealPowQuotient A B e ≃ₐ[ResidueField A]
    (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) :=
    { Ideal.quotEquivOfEq hI with
      commutes' := fun r => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        rfl }
  have hmk : e₂ (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ b := rfl
  have hconj := Algebra.trace_eq_of_algEquiv e₂ (Ideal.Quotient.mk _ b)
  rw [hmk] at hconj
  have hres : residue A (Algebra.intTrace A B b) =
    Algebra.trace (ResidueField A)
      (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))
      (Ideal.Quotient.mk _ b) := hMathlib.symm
  rwa [hres, hconj]

/--
[intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowQuotientTrace.lean)
-/
@[path]
lemma intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  {e : ℕ}
-- given
  (heUnit : IsUnit (e : B))
  (he : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ e) :
-- imply
  Function.Surjective (Algebra.intTrace A B) := by
-- proof
  obtain ⟨r, hr⟩ := Algebra.trace_surjective
    (ResidueField A) (ResidueField B) (1 : ResidueField A)
  obtain ⟨b, hb⟩ := residue_surjective r
  have heUnitA : IsUnit (e : A) := by
    rw [← isUnit_map_iff (algebraMap A B) (e : A)]
    simpa only [map_natCast] using heUnit
  have hbTrace : IsUnit (Algebra.intTrace A B b) := by
    rw [← residue_ne_zero_iff_isUnit]
    rw [residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow
      A B e he b, hb, hr]
    simpa only [nsmul_eq_mul, mul_one, map_natCast] using
      (heUnitA.map (residue A)).ne_zero
  intro a
  obtain ⟨u, hu⟩ := hbTrace
  refine ⟨(a * ↑u⁻¹) • b, ?_⟩
  rw [map_smul, ← hu, smul_eq_mul, mul_assoc, Units.inv_mul, mul_one]


-- created on 2026-10-20
-- updated on 2026-10-23
