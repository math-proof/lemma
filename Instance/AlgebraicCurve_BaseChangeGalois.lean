-- Carved from Lemma/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean: instance decls only.
-- Helpers for instance proofs live here (no Definitions stub import → no cycle).
-- Entangled defs smulValuationSubringEquiv / smulResidueRingEquiv / degZeroSMulHom are PUBLIC
-- so Definitions theorems and GluedPic0 can rw against the same constants the instances use.
-- Theorems remain private where only needed for elaboration order.
import Def.AlgebraicCurve_BaseChangeGalois
import Instance.AlgebraicCurve_DivisorClassGroup
import Mathlib.Algebra.Ring.Action.End
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.ZMod

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

namespace SemilinearAut

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

instance : MulSemiringAction (SemilinearAut K F) F where
  smul g x := toRingAut g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero g := map_zero (toRingAut g)
  smul_add g := map_add (toRingAut g)
  smul_one g := map_one (toRingAut g)
  smul_mul g := map_mul (toRingAut g)

-- Local helpers for Place SMul (public copies stay in Definitions).
private theorem smul_algebraMap (g : SemilinearAut K F) (a : K) :
    g • algebraMap K F a = algebraMap K F (baseAut g a) :=
  commutes g a

open scoped Pointwise

private theorem pointwise_smul_top (g : SemilinearAut K F) :
    g • (⊤ : ValuationSubring F) = ⊤ := by
  ext x
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact ⟨fun _ => ValuationSubring.mem_top x, fun _ => ValuationSubring.mem_top _⟩

def smulValuationSubringEquiv (g : SemilinearAut K F) (A : ValuationSubring F) :
    A ≃+* (g • A : ValuationSubring F) where
  toFun x := ⟨g • (x : F), ValuationSubring.smul_mem_pointwise_smul g (x : F) A x.2⟩
  invFun y := ⟨g⁻¹ • (y : F),
    (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem (g := g) (S := A)
      (x := (y : F))).mp y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

instance : SMul (SemilinearAut K F) (Place K F) where
  smul g v :=
    { toValuationSubring := g • v.toValuationSubring
      algebraMap_mem' := fun a => by
        have h := ValuationSubring.smul_mem_pointwise_smul g
          (algebraMap K F ((baseAut g).symm a)) v.toValuationSubring
          (v.algebraMap_mem' ((baseAut g).symm a))
        rwa [smul_algebraMap, RingEquiv.apply_symm_apply] at h
      ne_top' := fun h => v.ne_top' <| by
        have h2 := congrArg (g⁻¹ • ·) h
        simpa [pointwise_smul_top] using h2
      isPrincipalIdealRing' :=
        IsPrincipalIdealRing.of_surjective
          (smulValuationSubringEquiv g v.toValuationSubring : _ ≃+* _)
          (smulValuationSubringEquiv g v.toValuationSubring).surjective }

instance : MulAction (SemilinearAut K F) (Place K F) where
  one_smul v := by
    ext1
    change (1 : SemilinearAut K F) • v.toValuationSubring = v.toValuationSubring
    rw [one_smul]
  mul_smul g h v := by
    ext1
    change (g * h) • v.toValuationSubring = g • h • v.toValuationSubring
    rw [mul_smul]

-- Local helpers for Pic0 SMul (public copies stay in Definitions).
private theorem ord_smul (g : SemilinearAut K F) (v : Place K F) (f : F) :
    (g • v).ord (g • f) = v.ord f := by
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

def smulResidueRingEquiv (g : SemilinearAut K F) (v : Place K F) :
    v.ResidueField ≃+* (g • v).ResidueField :=
  IsLocalRing.ResidueField.mapEquiv (smulValuationSubringEquiv g v.toValuationSubring)

private theorem smulResidueRingEquiv_algebraMap (g : SemilinearAut K F) (v : Place K F) (a : K) :
    smulResidueRingEquiv g v (algebraMap K v.ResidueField a)
      = algebraMap K (g • v).ResidueField (baseAut g a) := by
  have h3 : (smulValuationSubringEquiv g v.toValuationSubring)
        (algebraMap K v.toValuationSubring a)
      = algebraMap K (g • v).toValuationSubring (baseAut g a) := by
    ext
    change g • (algebraMap K F a) = algebraMap K F (baseAut g a)
    exact smul_algebraMap g a
  show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = IsLocalRing.residue _ _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  exact congrArg _ h3

private theorem deg_smul (g : SemilinearAut K F) (v : Place K F) : (g • v).deg = v.deg := by
  refine (Algebra.finrank_eq_of_equiv_equiv (baseAut g) (smulResidueRingEquiv g v) ?_).symm
  ext a
  simpa using (smulResidueRingEquiv_algebraMap g v a).symm

instance : DistribMulAction (SemilinearAut K F) (Divisor K F) :=
  Finsupp.comapDistribMulAction

private theorem divisor_smul_def (g : SemilinearAut K F) (D : Divisor K F) :
    g • D = Finsupp.mapDomain (g • ·) D := rfl

private theorem smul_single (g : SemilinearAut K F) (v : Place K F) (n : ℤ) :
    g • Finsupp.single v n = Finsupp.single (g • v) n := by
  rw [divisor_smul_def, Finsupp.mapDomain_single]

private theorem divisor_smul_apply_smul (g : SemilinearAut K F) (D : Divisor K F) (v : Place K F) :
    (g • D) (g • v) = D v := by
  rw [divisor_smul_def]
  exact Finsupp.mapDomain_apply_of_injective (MulAction.injective g) D v

private theorem divisor_smul_apply (g : SemilinearAut K F) (D : Divisor K F) (w : Place K F) :
    (g • D) w = D (g⁻¹ • w) := by
  have : (g • D) (g • (g⁻¹ • w)) = D (g⁻¹ • w) := divisor_smul_apply_smul g D (g⁻¹ • w)
  rwa [smul_inv_smul] at this

private theorem degree_smul (g : SemilinearAut K F) (D : Divisor K F) :
    Divisor.degree (g • D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
      rw [smul_add, map_add, map_add, ih, smul_single, Divisor.degree_single,
        Divisor.degree_single, deg_smul]

private theorem smul_mem_degZero (g : SemilinearAut K F) {D : Divisor K F}
    (hD : D ∈ Divisor.degZero (K := K) (F := F)) :
    g • D ∈ Divisor.degZero (K := K) (F := F) := by
  rwa [Divisor.mem_degZero, degree_smul]

private theorem smul_mem_principal (g : SemilinearAut K F) {D : Divisor K F}
    (hD : D ∈ Divisor.principal (K := K) (F := F)) :
    g • D ∈ Divisor.principal (K := K) (F := F) := by
  obtain ⟨f, hf, hD⟩ := hD
  refine ⟨g • f, ?_, fun w => ?_⟩
  · change toRingAut g f ≠ 0
    exact (RingEquiv.map_ne_zero_iff _).mpr hf
  rw [divisor_smul_apply, hD (g⁻¹ • w)]
  have h := ord_smul g (g⁻¹ • w) f
  rw [smul_inv_smul] at h
  exact h.symm

def degZeroSMulHom (g : SemilinearAut K F) :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
  ((DistribSMul.toAddMonoidHom (Divisor K F) g).domRestrict
    (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => smul_mem_degZero g D.2)

private theorem coe_degZeroSMulHom (g : SemilinearAut K F)
    (D : Divisor.degZero (K := K) (F := F)) :
    (degZeroSMulHom g D : Divisor K F) = g • (D : Divisor K F) := rfl

instance : SMul (SemilinearAut K F) (Pic0 K F) where
  smul g := QuotientAddGroup.map _ _ (degZeroSMulHom g) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact smul_mem_principal g hD)

private theorem pic0_smul_mk (g : SemilinearAut K F) (D : Divisor.degZero (K := K) (F := F)) :
    g • (Pic0.mk D) = Pic0.mk (degZeroSMulHom g D) := rfl

instance : DistribMulAction (SemilinearAut K F) (Pic0 K F) where
  one_smul x := by
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
    rw [pic0_smul_mk]
    exact congrArg Pic0.mk (Subtype.ext (by rw [coe_degZeroSMulHom, one_smul]))
  mul_smul g h x := by
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
    rw [pic0_smul_mk, pic0_smul_mk, pic0_smul_mk]
    exact congrArg Pic0.mk (Subtype.ext (by simp only [coe_degZeroSMulHom]; rw [mul_smul]))
  smul_zero g := by
    show g • Pic0.mk 0 = Pic0.mk 0
    rw [pic0_smul_mk]
    exact congrArg Pic0.mk (map_zero _)
  smul_add g x y := by
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
    obtain ⟨E, rfl⟩ := Pic0.mk_surjective y
    show g • Pic0.mk (D + E) = Pic0.mk (degZeroSMulHom g D) + Pic0.mk (degZeroSMulHom g E)
    rw [pic0_smul_mk]
    exact congrArg Pic0.mk (map_add _ _ _)

-- Local helpers for torsion SMul (public copies stay in Definitions).
private theorem smul_zsmul (g : SemilinearAut K F) (m : ℤ) (x : Pic0 K F) :
    g • (m • x) = m • (g • x) :=
  map_zsmul (DistribSMul.toAddMonoidHom (Pic0 K F) g) m x

private theorem smul_mem_torsion (g : SemilinearAut K F) {n : ℕ} {x : Pic0 K F}
    (hx : x ∈ Pic0.torsion K F n) : g • x ∈ Pic0.torsion K F n := by
  rw [Pic0.mem_torsion] at hx ⊢
  rw [← smul_zsmul, hx]
  exact smul_zero (A := Pic0 K F) g

instance instSMulTorsion (n : ℕ) : SMul (SemilinearAut K F) (Pic0.torsion K F n) :=
  ⟨fun g x => ⟨g • (x : Pic0 K F), smul_mem_torsion g x.property⟩⟩

instance instDistribMulActionTorsion (n : ℕ) :
    DistribMulAction (SemilinearAut K F) (Pic0.torsion K F n) where
  one_smul x := Subtype.ext <| one_smul _ (x : Pic0 K F)
  mul_smul g h x := Subtype.ext <| mul_smul g h (x : Pic0 K F)
  smul_zero g := Subtype.ext <| smul_zero (A := Pic0 K F) g
  smul_add g x y := Subtype.ext <| smul_add g (x : Pic0 K F) (y : Pic0 K F)

end SemilinearAut

namespace Pic0

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

instance instModuleZModTorsion (n : ℕ) : Module (ZMod n) (torsion K F n) :=
  AddCommGroup.zmodModule fun x => by
    apply Subtype.ext
    change ((n • x : torsion K F n) : Pic0 K F) = 0
    rw [AddSubgroupClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℤ n (x : Pic0 K F)]
    exact mem_torsion.mp x.property

end Pic0

namespace SemilinearAut

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

instance instSMulCommClassZModTorsion (n : ℕ) :
    SMulCommClass (SemilinearAut K F) (ZMod n) (Pic0.torsion K F n) where
  smul_comm g c x :=
    ZMod.map_smul (DistribSMul.toAddMonoidHom (Pic0.torsion K F n) g) c x

end SemilinearAut

end AlgebraicCurve
