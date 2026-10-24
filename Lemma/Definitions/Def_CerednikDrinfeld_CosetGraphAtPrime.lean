import Lemma.Definitions.Def_Submodule_LocalBox
import Lemma.Definitions.Def_CerednikDrinfeld_MumfordPeriod

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace CerednikDrinfeld.CosetGraph

variable {a b : ℚ}

abbrev Loc (a b : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : Type := ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ

def toLoc (v : HeightOneSpectrum (𝓞 ℚ)) : (ℍ[ℚ, a, b])ˣ →* (Loc a b v)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft : ℍ[ℚ, a, b] →ₐ[ℚ] Loc a b v).toRingHom.toMonoidHom

def scalarUnits (v : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (Loc a b v)ˣ :=
  (Units.map (Algebra.TensorProduct.includeRight : v.adicCompletion ℚ →ₐ[ℚ] Loc a b v).toRingHom.toMonoidHom).range

def level (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (Loc a b v)ˣ :=
  Subgroup.closure (Submodule.localBoxUnits R v) ⊔ scalarUnits v

abbrev Vert (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Type := (Loc a b v)ˣ ⧸ level R v

def graph (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (nv : (Loc a b v)ˣ) : SimpleGraph (Vert R v) where
  Adj x y := x ≠ y ∧ ∃ g : (Loc a b v)ˣ, ∃ k ∈ level R v,
    (x = (g : Vert R v) ∧ y = ((g * k * nv : (Loc a b v)ˣ) : Vert R v)) ∨
      (y = (g : Vert R v) ∧ x = ((g * k * nv : (Loc a b v)ˣ) : Vert R v))
  symm := ⟨by
    rintro x y ⟨hne, g, k, hk, h⟩
    exact ⟨hne.symm, g, k, hk, h.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def awayUnits (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (ℍ[ℚ, a, b])ˣ :=
  ⨅ (w : HeightOneSpectrum (𝓞 ℚ)) (_ : w ≠ v), (Subgroup.closure (Submodule.localBoxUnits R w)).comap (toLoc w)

instance vertMulAction (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) :
    MulAction (ℍ[ℚ, a, b])ˣ (Vert R v) :=
  MulAction.compHom (Vert R v) (toLoc (a := a) (b := b) v)

theorem smul_vert_mk (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (γ : (ℍ[ℚ, a, b])ˣ) (g : (Loc a b v)ˣ) :
    γ • ((g : (Loc a b v)ˣ) : Vert R v) = ((toLoc v γ * g : (Loc a b v)ˣ) : Vert R v) := rfl

instance awayVertMulAction (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) :
    MulAction (awayUnits R v) (Vert R v) := inferInstance

def actionKer (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (awayUnits R v) :=
  (MulAction.toPermHom (awayUnits R v) (Vert R v)).ker

instance actionKer_normal (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : (actionKer R v).Normal :=
  MonoidHom.normal_ker _

abbrev ProjAwayUnits (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Type :=
  (awayUnits R v) ⧸ actionKer R v

instance projVertMulAction (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) :
    MulAction (ProjAwayUnits R v) (Vert R v) :=
  MulAction.compHom (Vert R v) (QuotientGroup.kerLift (MulAction.toPermHom (awayUnits R v) (Vert R v)))

theorem mk_smul_vert (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (γ : awayUnits R v) (x : Vert R v) :
    (QuotientGroup.mk γ : ProjAwayUnits R v) • x = γ • x := rfl

theorem coe_smul_vert_mk (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (γ : awayUnits R v)
    (g : (Loc a b v)ˣ) :
    γ • ((g : (Loc a b v)ˣ) : Vert R v) = ((toLoc v (γ : (ℍ[ℚ, a, b])ˣ) * g : (Loc a b v)ˣ) : Vert R v) := rfl

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
