-- Carved from Lemma/Definitions/Def_CerednikDrinfeld_MumfordQuotient.lean: instance decls only.
import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.Ring.Action.Group
import Instance.AlgebraicCurve_BaseChangeGalois
import Lemma.CerednikDrinfeld.MumfordVertexType
import Lemma.CerednikDrinfeld.MumfordQuotient

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld.Mumford

section Generic

variable (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
variable [MulSemiringAction G M] [SMulCommClass G K M]

scoped instance fracMulSemiringAction [IsDomain M] : MulSemiringAction G (FractionRing M) where
  smul g x := fracAct G M g x
  one_smul x := by show fracAct G M 1 x = x; rw [fracAct_one]; rfl
  mul_smul g h x := by show fracAct G M (g * h) x = fracAct G M g (fracAct G M h x); rw [fracAct_mul]; rfl
  smul_zero g := map_zero (fracAct G M g)
  smul_add g x y := map_add (fracAct G M g) x y
  smul_one g := map_one (fracAct G M g)
  smul_mul g x y := map_mul (fracAct G M g) x y

scoped instance fracSMulCommClass [IsDomain M] : SMulCommClass G K (FractionRing M) :=
  ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', smul_algebraMap_const]⟩

instance invariantFieldAlgebra [IsDomain M] : Algebra K ↥(invariantField K G M) :=
  (invariantIntermediateField K G M).algebra

instance invariantFieldOfAlgebra [IsDomain M] (Γ : Subgroup G) : Algebra K ↥(invariantFieldOf K G M Γ) :=
  (invariantIntermediateFieldOf K G M Γ).algebra

namespace AmbientSemilinearAut

variable {K G M}

section Transport


instance instGroup : Group (AmbientSemilinearAut K G M) where
  mul s t :=
    { base := t.base.trans s.base
      map := t.map.trans s.map
      map_algebraMap := fun c => by
        rw [RingEquiv.coe_trans, Function.comp_apply, t.map_algebraMap, s.map_algebraMap]; rfl
      map_smul := fun g m => by
        rw [RingEquiv.coe_trans, Function.comp_apply, t.map_smul, s.map_smul]; rfl }
  one :=
    { base := RingEquiv.refl K
      map := RingEquiv.refl M
      map_algebraMap := fun _ => rfl
      map_smul := fun _ _ => rfl }
  inv s :=
    { base := s.base.symm
      map := s.map.symm
      map_algebraMap := fun c => by
        apply s.map.injective
        rw [RingEquiv.apply_symm_apply, s.map_algebraMap, RingEquiv.apply_symm_apply]
      map_smul := fun g m => by
        apply s.map.injective
        rw [RingEquiv.apply_symm_apply, s.map_smul, RingEquiv.apply_symm_apply] }
  mul_assoc s t u := ext rfl rfl
  one_mul s := ext (RingEquiv.ext fun _ => rfl) (RingEquiv.ext fun _ => rfl)
  mul_one s := ext (RingEquiv.ext fun _ => rfl) (RingEquiv.ext fun _ => rfl)
  inv_mul_cancel s := ext (RingEquiv.ext fun x => s.base.symm_apply_apply x) (RingEquiv.ext fun x => s.map.symm_apply_apply x)

end Transport


end AmbientSemilinearAut

end Generic


end CerednikDrinfeld.Mumford

end
