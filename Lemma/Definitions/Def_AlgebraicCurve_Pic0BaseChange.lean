import Lemma.Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Lemma.Definitions.Def_ModularCurve_DegeneracyVp

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section Equivariance

open scoped Pointwise

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F'] [Algebra K F] [Algebra K' F'] [Algebra F F']
  {σ : F ≃ₐ[K] F} {σ' : F' ≃ₐ[K'] F'}

theorem algebraMap_inv_apply_of_forall_algebraMap_apply
    (hσ : ∀ f : F, algebraMap F F' (σ f) = σ' (algebraMap F F' f)) (f : F) :
    algebraMap F F' (σ⁻¹ f) = σ'⁻¹ (algebraMap F F' f) := by
  rw [AlgEquiv.aut_inv, AlgEquiv.aut_inv]
  apply σ'.injective
  rw [← hσ (σ.symm f), σ.apply_symm_apply, σ'.apply_symm_apply]

variable [Algebra K K'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']

theorem Place.restrictConstants_smul (hσ : ∀ f : F, algebraMap F F' (σ f) = σ' (algebraMap F F' f))
    (w : Place K' F') :
    Place.restrictConstants F (K := K) (σ' • w) = σ • Place.restrictConstants F (K := K) w := by
  apply Place.ext
  ext f
  rw [Place.restrictConstants_toValuationSubring, Place.smul_toValuationSubring, Place.smul_toValuationSubring,
    Place.restrictConstants_toValuationSubring, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_comap, AlgEquiv.smul_def, AlgEquiv.smul_def,
    algebraMap_inv_apply_of_forall_algebraMap_apply hσ f]

theorem Place.ramificationIndex_forgetConstants_smul
    (hσ : ∀ f : F, algebraMap F F' (σ f) = σ' (algebraMap F F' f)) (w : Place K' F') :
    Place.ramificationIndex (F := F) (Place.forgetConstants (K := K) (σ' • w)) =
      Place.ramificationIndex (F := F) (Place.forgetConstants (K := K) w) := by
  obtain ⟨π, hπ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (Place.restrictConstants F (K := K) w).toValuationSubring
  have h1 : (Place.restrictConstants F (K := K) w).ord (π : F) = 1 :=
    (Place.restrictConstants F (K := K) w).ord_coe_irreducible hπ
  have h2 : (Place.restrictConstants F (K := K) (σ' • w)).ord (σ (π : F)) = 1 := by
    rw [Place.restrictConstants_smul hσ w, Place.ord_smul, h1]
  have h3 := Place.ord_restrictConstants (K := K) (σ' • w) (σ (π : F))
  rw [h2, mul_one, hσ, Place.ord_smul, Place.ord_restrictConstants (K := K) w (π : F), h1, mul_one] at h3
  exact_mod_cast h3.symm

theorem Divisor.pullbackConstants_smul [HasPrincipalDivisors K' F']
    (hσ : ∀ f : F, algebraMap F F' (σ f) = σ' (algebraMap F F' f)) (D : Divisor K F) :
    Divisor.pullbackConstants K' F' (σ • D) = σ' • Divisor.pullbackConstants K' F' D := by
  have hinv := algebraMap_inv_apply_of_forall_algebraMap_apply hσ
  ext w
  rw [Divisor.smul_apply, Divisor.pullbackConstants_apply, Divisor.pullbackConstants_apply, Divisor.smul_apply,
    Place.restrictConstants_smul hinv w, Place.ramificationIndex_forgetConstants_smul hinv w]

end Equivariance

section ClassGroup

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K' F'] [ConstantFieldDegreeFormula K K' F F']

variable (K K' F F') in

def Pic0.degZeroBaseChangeHom :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K') (F := F') :=
  ((Divisor.pullbackConstants K' F').domRestrict (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => Divisor.pullbackConstants_mem_degZero D.2)

theorem Pic0.coe_degZeroBaseChangeHom (D : Divisor.degZero (K := K) (F := F)) :
    (degZeroBaseChangeHom K K' F F' D : Divisor K' F') = Divisor.pullbackConstants K' F' (D : Divisor K F) :=
  rfl

variable (K K' F F') in

def Pic0.baseChange : Pic0 K F →+ Pic0 K' F' :=
  QuotientAddGroup.map _ _ (degZeroBaseChangeHom K K' F F') (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.pullbackConstants_mem_principal hD)

@[simp]
theorem Pic0.baseChange_mk (D : Divisor.degZero (K := K) (F := F)) :
    Pic0.baseChange K K' F F' (Pic0.mk D) =
      Pic0.mk ⟨Divisor.pullbackConstants K' F' (D : Divisor K F), Divisor.pullbackConstants_mem_degZero D.2⟩ :=
  rfl

theorem Pic0.baseChange_smul {σ : F ≃ₐ[K] F} {σ' : F' ≃ₐ[K'] F'}
    (hσ : ∀ f : F, algebraMap F F' (σ f) = σ' (algebraMap F F' f)) (x : Pic0 K F) :
    Pic0.baseChange K K' F F' (σ • x) = σ' • Pic0.baseChange K K' F F' x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.smul_mk, Pic0.baseChange_mk, Pic0.baseChange_mk, Pic0.smul_mk]
  exact congrArg Pic0.mk (Subtype.ext (Divisor.pullbackConstants_smul hσ (D : Divisor K F)))

end ClassGroup

end AlgebraicCurve

namespace ModularCurve

section Intertwining

variable (p : ℕ) [Fact p.Prime] {J J' : Type} [AddCommGroup J] [AddCommGroup J']
  {G G' : Type} [Monoid G] [Monoid G'] [DistribMulAction G J] [DistribMulAction G' J']

theorem tateMapLin_comp_rep (f : J →+ J') (g : G) (g' : G') (h : ∀ x : J, f (g • x) = g' • f x) :
    tateMapLin p f ∘ₗ TateModule.rep p J G g = TateModule.rep p J' G' g' ∘ₗ tateMapLin p f := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
  exact h ((x : ℕ → J) n)

theorem vpMap_comp_rationalGaloisRep (f : J →+ J') (g : G) (g' : G') (h : ∀ x : J, f (g • x) = g' • f x) :
    vpMap p f ∘ₗ rationalGaloisRep p J G g = rationalGaloisRep p J' G' g' ∘ₗ vpMap p f := by
  rw [rationalGaloisRep_apply, rationalGaloisRep_apply, vpMap, ← LinearMap.baseChange_comp,
    ← LinearMap.baseChange_comp, tateMapLin_comp_rep p f g g' h]

end Intertwining

end ModularCurve

end
