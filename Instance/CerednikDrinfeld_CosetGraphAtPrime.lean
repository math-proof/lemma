-- Carved from Lemma/Definitions/Def_CerednikDrinfeld_CosetGraphAtPrime.lean: instance decls only.
import Instance.Submodule_LocalBox
import Class.CerednikDrinfeld_MumfordPeriod
import Lemma.CerednikDrinfeld.CosetGraphAtPrime

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace CerednikDrinfeld.CosetGraph

variable {a b : ℚ}

instance vertMulAction (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) :
    MulAction (ℍ[ℚ, a, b])ˣ (Vert R v) :=
  MulAction.compHom (Vert R v) (toLoc (a := a) (b := b) v)

instance awayVertMulAction (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) :
    MulAction (awayUnits R v) (Vert R v) := inferInstance

instance actionKer_normal (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : (actionKer R v).Normal :=
  MonoidHom.normal_ker _

instance projVertMulAction (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) :
    MulAction (ProjAwayUnits R v) (Vert R v) :=
  MulAction.compHom (Vert R v) (QuotientGroup.kerLift (MulAction.toPermHom (awayUnits R v) (Vert R v)))

instance projGraphAction (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (nv : (Loc a b v)ˣ) :
    Mumford.GraphAction (ProjAwayUnits R v) (graph R v nv) where
  smul_adj := by
    intro q x y hxy
    induction q using QuotientGroup.induction_on with
    | H γ =>
      rw [mk_smul_vert, mk_smul_vert]
      obtain ⟨hne, g, k, hk, h⟩ := hxy
      refine ⟨fun e => hne (smul_left_cancel γ e), toLoc v (γ : (ℍ[ℚ, a, b])ˣ) * g, k, hk, ?_⟩
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; exact ⟨coe_smul_vert_mk R v γ g, by rw [coe_smul_vert_mk, mul_assoc, mul_assoc, mul_assoc]⟩
      · right; exact ⟨coe_smul_vert_mk R v γ g, by rw [coe_smul_vert_mk, mul_assoc, mul_assoc, mul_assoc]⟩

end CerednikDrinfeld.CosetGraph

end
