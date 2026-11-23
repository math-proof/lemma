import Mathlib
import Def.FormalGroup_NegV2
import Def.CerednikDrinfeld_SpecialFormalModule
import Notation.CerednikDrinfeld_LubinTateModule

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPowerSeries

namespace CerednikDrinfeld.LubinTateLemma

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [CharP k p]

variable (p k)

def fvec (τ : Type*) : τ → MvPowerSeries τ (WittVector p k) :=
  fun s => C (p : WittVector p k) * X s + X s ^ Fintype.card k

def Comm {τ : Type*} (φ : MvPowerSeries τ (WittVector p k)) : Prop :=
  C (p : WittVector p k) * φ + φ ^ Fintype.card k = subst (fvec p k τ) φ

def defect {τ : Type*} (θ : MvPowerSeries τ (WittVector p k)) : MvPowerSeries τ (WittVector p k) :=
  C (p : WittVector p k) * θ + θ ^ Fintype.card k - subst (fvec p k τ) θ

variable {p k}


section Divisible

variable {τ : Type*}

include p in

end Divisible


section Exists

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

open scoped Classical in

def pdiv (x : WittVector p k) : WittVector p k :=
  if h : ∃ y : WittVector p k, x = (p : WittVector p k) * y then h.choose else 0

def corr (θ : MvPowerSeries τ (WittVector p k)) (n : ℕ) : MvPowerSeries τ (WittVector p k) :=
  fun d => if d.degree = n + 2 then
    -(((isUnit_one_sub_pow (p := p) (k := k) n).unit⁻¹ : (WittVector p k)ˣ) : WittVector p k)
      * pdiv (coeff d (defect p k θ)) else 0

def approx (c : τ → WittVector p k) : ℕ → MvPowerSeries τ (WittVector p k)
  | 0 => ∑ s, C (c s) * X s
  | n + 1 => approx c n + corr (approx c n) n

def ltSeries (c : τ → WittVector p k) : MvPowerSeries τ (WittVector p k) :=
  fun d => coeff d (approx c d.degree)

end Exists

end CerednikDrinfeld.LubinTateLemma

end

universe u v in
set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace CerednikDrinfeld.LubinTate

universe u v

variable {p : ℕ} [Fact p.Prime]

open scoped CerednikDrinfeld_LubinTateModule

variable (p)

def fvec (τ : Type*) : τ → MvPowerSeries τ 𝕆 :=
  fun s => C (p : 𝕆) * X s + X s ^ 𝔮

def Comm {τ : Type*} (φ : MvPowerSeries τ 𝕆) : Prop :=
  C (p : 𝕆) * φ + φ ^ 𝔮 = subst (fvec p τ) φ

def lt (τ : Type*) [Finite τ] (c : τ → 𝕆) : MvPowerSeries τ 𝕆 :=
  (lt_existsUnique p τ c).exists.choose

variable {p}


section Sigma

variable (p)

def sigmaSeries : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆 := lt p (Fin 1 ⊕ Fin 1) fun _ => 1

def act₁ (a : 𝕆) : MvPowerSeries (Fin 1) 𝕆 := lt p (Fin 1) fun _ => a

variable {p}

variable (p) in

def sigma : MvFormalGroup 1 𝕆 where
  toPowerSeries := fun _ => sigmaSeries p
  constantCoeff_eq_zero := fun _ => constantCoeff_sigmaSeries
  coeff_single_inl i j := by
    rw [coeff_single_sigmaSeries, if_pos (Subsingleton.elim i j)]
  coeff_single_inr i j := by
    rw [coeff_single_sigmaSeries, if_pos (Subsingleton.elim i j)]
  assoc i := by
end Sigma

section Reduction

variable {B : Type u} [CommRing B]

variable (j : Zp2 p →+* B)

def sigmaBar : MvFormalGroup 1 B := (sigma p).map j

def rhoEnd (a : 𝕆) : MvFormalGroup.End (sigmaBar j) where
  toPowerSeries := fun _ => MvPowerSeries.map j (act₁ p a)
  constantCoeff_eq_zero := fun _ => by rw [constantCoeff_map, constantCoeff_act₁, map_zero]
  subst_eq i := by
    rw [Fin.fin_one_eq_zero i]
    exact map_homIdentity₁ j (fun _ => constantCoeff_sigmaSeries) (constantCoeff_act₁ a)
      (subst_sigma_act₁ a)

def rho : 𝕆 →+* MvFormalGroup.End (sigmaBar j) where
  toFun := rhoEnd j
  map_one' := by
    apply MvFormalGroup.Hom.ext
    funext i
    rw [rhoEnd_toPowerSeries, act₁_one, MvPowerSeries.map_X, end_toPowerSeries_one,
      Fin.fin_one_eq_zero i]
  map_mul' a b := by
    apply MvFormalGroup.Hom.ext
    funext i
    rw [rhoEnd_toPowerSeries, end_toPowerSeries_mul, act₁_mul,
      map_subst (hasSubst_fin1 (constantCoeff_act₁ b))]
    rfl
  map_zero' := by
    apply MvFormalGroup.Hom.ext
    funext i
    rw [rhoEnd_toPowerSeries, act₁_zero, map_zero, end_toPowerSeries_zero]
  map_add' a b := by
    apply MvFormalGroup.Hom.ext
    funext i
    have hab : HasSubst (Sum.elim (fun _ : Fin 1 => act₁ p a) fun _ : Fin 1 => act₁ p b) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (l | l) <;> exact constantCoeff_act₁ _
    rw [rhoEnd_toPowerSeries, end_toPowerSeries_add, act₁_add, map_subst hab]
    dsimp only
    rw [sigmaBar_toPowerSeries]
    congr 1
    funext s
    rcases s with l | l <;> rfl

variable [CharP B p]

def phi : MvFormalGroup.End (sigmaBar j) where
  toPowerSeries := fun _ => (X 0 : MvPowerSeries (Fin 1) B) ^ p
  constantCoeff_eq_zero := fun _ => by rw [map_pow, constantCoeff_X, zero_pow hp0]
  subst_eq i := by
    rw [Fin.fin_one_eq_zero i, sigmaBar_toPowerSeries, subst_pow (sigmaBar j).hasSubst_toPowerSeries,
      subst_X (sigmaBar j).hasSubst_toPowerSeries, sigmaBar_toPowerSeries, sigmaBar_pow_p]
    congr 1
    funext s
    rcases s with l | l
    · rw [Fin.fin_one_eq_zero l, Sum.elim_inl,
        subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
        subst_X (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
    · rw [Fin.fin_one_eq_zero l, Sum.elim_inr,
        subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
        subst_X (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]

end Reduction

end CerednikDrinfeld.LubinTate

end
