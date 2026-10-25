-- Carved from Lemma/Definitions/Def_CerednikDrinfeld_DrinfeldHolomorphic.lean: instance decls only.
import Instance.CerednikDrinfeld_DrinfeldUpperHalfPlane
import Instance.CerednikDrinfeld_MumfordQuotient
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Algebra.Polynomial.Eval.Defs
import Lemma.CerednikDrinfeld.DrinfeldHolomorphic

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups
open Filter CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

namespace CerednikDrinfeld.Omega

variable (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

variable {K₀ K} (ϖ : PseudoUniformizer K₀ K)


instance holRingAlgebra : Algebra K ↥(holRing ϖ) := (holSubalgebra ϖ).algebra

section Actions

variable [DecidableEq K]

instance pglOmegaAction : MulAction PGL(2, K₀) ↥(upperHalfPlane K₀ K) where
  smul g z := ⟨pmoebius K₀ g (z : K), pmoebius_mem_upperHalfPlane K₀ z.2 g⟩
  one_smul z := Subtype.ext (pmoebius_one K₀ (z : K))
  mul_smul g h z := Subtype.ext (pmoebius_mul K₀ z.2 g h)


instance holRingAction : MulSemiringAction PGL(2, K₀) ↥(holRing ϖ) where
  smul g f := ⟨precomp g f, precomp_mem_holRing ϖ g f.2⟩
  one_smul f := Subtype.ext (precomp_one (f : ↥(upperHalfPlane K₀ K) → K))
  mul_smul g h f := Subtype.ext (precomp_mul g h (f : ↥(upperHalfPlane K₀ K) → K))
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

instance holRingSMulCommClass : SMulCommClass PGL(2, K₀) K ↥(holRing ϖ) :=
  ⟨fun _ _ _ => rfl⟩

namespace IsometricAut

instance instGroup : Group (IsometricAut K₀ K) where
  mul s t := ⟨t.toRingEquiv.trans s.toRingEquiv, fun x => by
    rw [RingEquiv.coe_trans, Function.comp_apply, s.isometry, t.isometry],
    fun a => by rw [RingEquiv.coe_trans, Function.comp_apply, t.fix, s.fix]⟩
  one := ⟨RingEquiv.refl K, fun _ => rfl, fun _ => rfl⟩
  inv s := ⟨s.toRingEquiv.symm, fun x => by
    conv_rhs => rw [← s.toRingEquiv.apply_symm_apply x]; rw [s.isometry],
    fun a => by apply s.toRingEquiv.injective; rw [RingEquiv.apply_symm_apply, s.fix]⟩
  mul_assoc s t u := ext rfl
  one_mul s := ext (RingEquiv.ext fun _ => rfl)
  mul_one s := ext (RingEquiv.ext fun _ => rfl)
  inv_mul_cancel s := ext (RingEquiv.ext fun x => s.toRingEquiv.symm_apply_apply x)

end IsometricAut

end Actions


section Glue

variable [DecidableEq K] {G : Type} [Group G] (ρ : G →* PGL(2, K₀))

instance HolRingOf.instCommRing : CommRing (HolRingOf ϖ ρ) := inferInstanceAs (CommRing ↥(holRing ϖ))
instance HolRingOf.instAlgebra : Algebra K (HolRingOf ϖ ρ) := inferInstanceAs (Algebra K ↥(holRing ϖ))
instance HolRingOf.instMulSemiringAction : MulSemiringAction G (HolRingOf ϖ ρ) :=
  MulSemiringAction.compHom ↥(holRing ϖ) ρ
instance HolRingOf.instSMulCommClass : SMulCommClass G K (HolRingOf ϖ ρ) :=
  ⟨fun g c f => smul_comm (ρ g) c (show ↥(holRing ϖ) from f)⟩

end Glue

end CerednikDrinfeld.Omega

end
