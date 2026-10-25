import Def.CohCarrier_Level
import Lemma.CohCarrier.HeckeData
import Inductive.CohCarrier_Gen

set_option autoImplicit false

noncomputable section

namespace CohCarrier

open CongruenceSubgroup
open scoped MatrixGroups

section Inst

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
variable (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]

def heckeTL (ℓ : ℕ) [NeZero ℓ] : Module.End 𝒪 (H1 M H 𝒪) where
  toFun φ := coresAdd _ (φ.comp (MonoidHom.toAdditive (conjL M H ℓ)))
  map_add' φ ψ := by
    have : (φ + ψ).comp (MonoidHom.toAdditive (conjL M H ℓ)) =
        φ.comp (MonoidHom.toAdditive (conjL M H ℓ)) + ψ.comp (MonoidHom.toAdditive (conjL M H ℓ)) := by
      ext; rfl
    rw [this, coresAdd_add]
  map_smul' r φ := by
    have : (r • φ).comp (MonoidHom.toAdditive (conjL M H ℓ)) =
        r • φ.comp (MonoidHom.toAdditive (conjL M H ℓ)) := by ext; rfl
    rw [this, coresAdd_smul]
    rfl

theorem heckeTL_apply (ℓ : ℕ) [NeZero ℓ] (φ : H1 M H 𝒪) :
    heckeTL M H 𝒪 ℓ φ = heckeT M H ℓ 𝒪 φ := rfl

theorem gamma0Units_surjective [NeZero M] : Function.Surjective (gamma0Units M) := by

  intro u
  have hAD : (((((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ) * ((u : ZMod M).val : ℤ) - 1 : ℤ) : ZMod M) = 0 := by
    simp
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAD
  let γ : SL(2, ℤ) := ⟨!![(((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ), k; (M : ℤ), ((u : ZMod M).val : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linarith⟩
  have hγ0 : γ ∈ Gamma0 M := by
    rw [Gamma0_mem]
    simp [γ]
  refine ⟨⟨γ, hγ0⟩, Units.ext ?_⟩
  simp only [gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Gamma0Map]
  simp [γ]

def diamondL [NeZero M] (d : (ZMod M)ˣ) : Module.End 𝒪 (H1 M H 𝒪) where
  toFun φ := diamondRaw M H 𝒪 (Classical.choose (gamma0Units_surjective M d)) φ
  map_add' φ ψ := map_add _ φ ψ
  map_smul' r φ := by ext; rfl

theorem diamondL_eq_diamondRaw [NeZero M] (d : (ZMod M)ˣ) (σ : Gamma0 M)
    (hσ : gamma0Units M σ = d) (φ : H1 M H 𝒪) :
    diamondL M H 𝒪 d φ = diamondRaw M H 𝒪 σ φ := by
  have hσ₀ : gamma0Units M (Classical.choose (gamma0Units_surjective M d)) = d :=
    Classical.choose_spec (gamma0Units_surjective M d)
  set σ₀ := Classical.choose (gamma0Units_surjective M d)

  have hκu : gamma0Units M (σ₀ * σ⁻¹) = 1 := by
    rw [map_mul, map_inv, hσ₀, hσ, mul_inv_cancel]
  have hκH : ((σ₀ * σ⁻¹ : Gamma0 M) : SL(2, ℤ)) ∈ GammaH M H := by
    rw [mem_GammaH_iff]
    exact ⟨(σ₀ * σ⁻¹).2, hκu ▸ one_mem H⟩
  set κ : ↥(GammaH M H) := ⟨((σ₀ * σ⁻¹ : Gamma0 M) : SL(2, ℤ)), hκH⟩ with hκdef

  have hconj : ∀ γ : ↥(GammaH M H),
      conjHom M H σ₀ γ = κ * conjHom M H σ γ * κ⁻¹ := by
    intro γ
    apply Subtype.ext
    simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, hκdef, Subgroup.coe_mul,
      InvMemClass.coe_inv, Subgroup.coe_mul]
    group

  ext γ
  show φ (Additive.ofMul (conjHom M H σ₀ (Additive.toMul γ))) = φ (Additive.ofMul (conjHom M H σ (Additive.toMul γ)))
  rw [hconj (Additive.toMul γ)]
  have hsplit : Additive.ofMul (κ * conjHom M H σ (Additive.toMul γ) * κ⁻¹) =
      Additive.ofMul κ + Additive.ofMul (conjHom M H σ (Additive.toMul γ)) + (-(Additive.ofMul κ)) := by
    rw [ofMul_mul, ofMul_mul, ofMul_inv]
  rw [hsplit, map_add, map_add, map_neg]
  abel

def opFamily [NeZero M] : Gen M S → Module.End 𝒪 (H1 M H 𝒪)
  | .T ℓ hℓ _ _ => haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeTL M H 𝒪 ℓ
  | .U q hq _ => haveI : NeZero q := ⟨hq.ne_zero⟩; heckeTL M H 𝒪 q
  | .dia d => diamondL M H 𝒪 d

def hdata [NeZero M]
    (hcomm : ∀ g h : Gen M S, opFamily M H S 𝒪 g * opFamily M H S 𝒪 h =
      opFamily M H S 𝒪 h * opFamily M H S 𝒪 g)
    (θbar : Gen M S → k) : HeckeData 𝒪 (H1 M H 𝒪) k where
  Gen := Gen M S
  op := opFamily M H S 𝒪
  comm := hcomm
  θbar := θbar

abbrev MLAt [NeZero M]
    (hcomm : ∀ g h : Gen M S, opFamily M H S 𝒪 g * opFamily M H S 𝒪 h =
      opFamily M H S 𝒪 h * opFamily M H S 𝒪 g)
    (θbar : Gen M S → k) : Type :=
  (hdata M H S 𝒪 k hcomm θbar).ML

example [NeZero M] (hcomm) (θbar : Gen M S → k) : Module 𝒪 (MLAt M H S 𝒪 k hcomm θbar) :=
  inferInstance

end Inst

end CohCarrier

end
