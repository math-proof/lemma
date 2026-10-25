-- Carved: SemilinearAut/toRingAut/baseAut/ofAlgAut -> Def.AlgebraicCurve_BaseChangeGalois
-- Instances -> Instance.AlgebraicCurve_BaseChangeGalois (this stub imports Instance).
-- Entangled defs smulValuationSubringEquiv / smulResidueRingEquiv / degZeroSMulHom
-- live in Instance (public) so instance proofs and GluedPic0 share one constant.
-- torsionRep / torsionRep_apply -> Def.AlgebraicCurve_BaseChangeGalois_TorsionRep
-- (imports Instance; Instance must NOT import that module).
import Def.AlgebraicCurve_BaseChangeGalois
import Def.AlgebraicCurve_BaseChangeGalois_TorsionRep
import Instance.AlgebraicCurve_BaseChangeGalois
import Lemma.AlgebraicCurve.DivisorClassGroup
import Mathlib.Algebra.Ring.Action.End
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace SemilinearAut


@[simp]
theorem smul_def (g : SemilinearAut K F) (x : F) : g • x = toRingAut g x := rfl

theorem inv_smul_def (g : SemilinearAut K F) (x : F) : g⁻¹ • x = (toRingAut g).symm x := rfl

theorem smul_algebraMap (g : SemilinearAut K F) (a : K) :
    g • algebraMap K F a = algebraMap K F (baseAut g a) :=
  commutes g a

@[simp]
theorem ofAlgAut_smul (σ : F ≃ₐ[K] F) (x : F) : ofAlgAut σ • x = σ x := rfl

end SemilinearAut

namespace SemilinearAut

open scoped Pointwise

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (g : SemilinearAut K F)

theorem pointwise_smul_top : g • (⊤ : ValuationSubring F) = ⊤ := by
  ext x
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact ⟨fun _ => ValuationSubring.mem_top x, fun _ => ValuationSubring.mem_top _⟩

-- smulValuationSubringEquiv: owned by Instance.AlgebraicCurve_BaseChangeGalois

@[simp]
theorem coe_smulValuationSubringEquiv_apply (A : ValuationSubring F) (x : A) :
    ((smulValuationSubringEquiv g A x : (g • A : ValuationSubring F)) : F) = g • (x : F) :=
  rfl


variable (v : Place K F)

@[simp]
theorem smul_toValuationSubring : (g • v).toValuationSubring = g • v.toValuationSubring :=
  rfl


theorem ord_smul (f : F) : (g • v).ord (g • f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ

  set n := v.ord f with hn

  set e := smulValuationSubringEquiv g v.toValuationSubring with he
  have hπ' : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have hu' : IsUnit (e (u : v.toValuationSubring)) := u.isUnit.map e
  have hcoeu : ((hu'.unit : (g • v).toValuationSubring) : F)
      = toRingAut g ((u : v.toValuationSubring) : F) := by
    rw [IsUnit.unit_spec]
    rfl
  have hcoeπ : ((e π : (g • v).toValuationSubring) : F) = toRingAut g (π : F) := rfl
  have key : toRingAut g f = ((hu'.unit : (g • v).toValuationSubring) : F)
      * (((e π : (g • v).toValuationSubring) : F) ^ n) := by
    rw [hcoeu, hcoeπ, hu, map_mul, map_zpow₀]
  rw [show g • f = toRingAut g f from rfl, key,
    (g • v).ord_unit_smul_zpow hu'.unit hπ' n]

-- smulResidueRingEquiv: owned by Instance.AlgebraicCurve_BaseChangeGalois

theorem smulResidueRingEquiv_algebraMap (a : K) :
    smulResidueRingEquiv g v (algebraMap K v.ResidueField a)
      = algebraMap K (g • v).ResidueField (baseAut g a) := by
  have h3 : (smulValuationSubringEquiv g v.toValuationSubring)
        (algebraMap K v.toValuationSubring a)
      = algebraMap K (g • v).toValuationSubring (baseAut g a) := by
    ext
    rw [coe_smulValuationSubringEquiv_apply, Place.coe_algebraMap, smul_algebraMap]
    exact (Place.coe_algebraMap (g • v) (baseAut g a)).symm
  show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = IsLocalRing.residue _ _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  exact congrArg _ h3

@[simp]
theorem deg_smul : (g • v).deg = v.deg := by
  refine (Algebra.finrank_eq_of_equiv_equiv (baseAut g) (smulResidueRingEquiv g v) ?_).symm
  ext a
  simpa using (smulResidueRingEquiv_algebraMap g v a).symm

end SemilinearAut

namespace SemilinearAut

open scoped Pointwise

variable {K F : Type*} [Field K] [Field F] [Algebra K F]


theorem divisor_smul_def (g : SemilinearAut K F) (D : Divisor K F) :
    g • D = Finsupp.mapDomain (g • ·) D := rfl

@[simp]
theorem smul_single (g : SemilinearAut K F) (v : Place K F) (n : ℤ) :
    g • Finsupp.single v n = Finsupp.single (g • v) n := by
  rw [divisor_smul_def, Finsupp.mapDomain_single]

theorem divisor_smul_apply_smul (g : SemilinearAut K F) (D : Divisor K F) (v : Place K F) :
    (g • D) (g • v) = D v := by
  rw [divisor_smul_def]
  exact Finsupp.mapDomain_apply_of_injective (MulAction.injective g) D v

theorem divisor_smul_apply (g : SemilinearAut K F) (D : Divisor K F) (w : Place K F) :
    (g • D) w = D (g⁻¹ • w) := by
  have : (g • D) (g • (g⁻¹ • w)) = D (g⁻¹ • w) := divisor_smul_apply_smul g D (g⁻¹ • w)
  rwa [smul_inv_smul] at this

@[simp]
theorem degree_smul (g : SemilinearAut K F) (D : Divisor K F) :
    Divisor.degree (g • D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
      rw [smul_add, map_add, map_add, ih, smul_single, Divisor.degree_single,
        Divisor.degree_single, deg_smul]

theorem smul_mem_degZero (g : SemilinearAut K F) {D : Divisor K F}
    (hD : D ∈ Divisor.degZero (K := K) (F := F)) :
    g • D ∈ Divisor.degZero (K := K) (F := F) := by
  rwa [Divisor.mem_degZero, degree_smul]

theorem smul_mem_principal (g : SemilinearAut K F) {D : Divisor K F}
    (hD : D ∈ Divisor.principal (K := K) (F := F)) :
    g • D ∈ Divisor.principal (K := K) (F := F) := by
  obtain ⟨f, hf, hD⟩ := hD
  refine ⟨g • f, by simpa using hf, fun w => ?_⟩
  rw [divisor_smul_apply, hD (g⁻¹ • w)]
  have h := ord_smul g (g⁻¹ • w) f
  rw [smul_inv_smul] at h
  exact h.symm

-- degZeroSMulHom: owned by Instance.AlgebraicCurve_BaseChangeGalois

@[simp]
theorem coe_degZeroSMulHom (g : SemilinearAut K F) (D : Divisor.degZero (K := K) (F := F)) :
    (degZeroSMulHom g D : Divisor K F) = g • (D : Divisor K F) := rfl


theorem pic0_smul_mk (g : SemilinearAut K F) (D : Divisor.degZero (K := K) (F := F)) :
    g • (Pic0.mk D) = Pic0.mk (degZeroSMulHom g D) := rfl


end SemilinearAut

end AlgebraicCurve

namespace AlgebraicCurve

namespace SemilinearAut

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem smul_zsmul (g : SemilinearAut K F) (m : ℤ) (x : Pic0 K F) :
    g • (m • x) = m • (g • x) :=
  map_zsmul (DistribSMul.toAddMonoidHom (Pic0 K F) g) m x

theorem smul_mem_torsion (g : SemilinearAut K F) {n : ℕ} {x : Pic0 K F}
    (hx : x ∈ Pic0.torsion K F n) : g • x ∈ Pic0.torsion K F n := by
  rw [Pic0.mem_torsion] at hx ⊢
  rw [← smul_zsmul, hx]
  exact smul_zero (A := Pic0 K F) g


@[simp]
theorem coe_torsion_smul {n : ℕ} (g : SemilinearAut K F) (x : Pic0.torsion K F n) :
    ((g • x : Pic0.torsion K F n) : Pic0 K F) = g • (x : Pic0 K F) := rfl


end SemilinearAut

end AlgebraicCurve
