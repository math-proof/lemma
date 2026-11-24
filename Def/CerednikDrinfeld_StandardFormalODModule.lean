module
public import Mathlib
public import Def.FormalGroup_NegV2
public import Def.CerednikDrinfeld_SpecialFormalModule
public import Def.CerednikDrinfeld_LubinTateModule
public import Def.FormalGroup_EndRingV2LinearPart
public import Abbrev.CerednikDrinfeld_StandardFormalODModule
public import Notation.CerednikDrinfeld_StandardFormalODModule


public section

section BoxBasisLemmaAppendix

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

noncomputable section

open MvPowerSeries

namespace CerednikDrinfeld.BoxBasisLemma

variable {R : Type*} [CommRing R] {g : ℕ} {N : Fin g → ℕ}

def InBox (N : Fin g → ℕ) (d : Fin g →₀ ℕ) : Prop := ∀ i, d i < N i

def boxKer (R : Type*) [CommRing R] (g : ℕ) (N : Fin g → ℕ) : Ideal (MvPowerSeries (Fin g) R) where
  carrier := {θ | ∀ d : Fin g →₀ ℕ, InBox N d → coeff d θ = 0}
  zero_mem' := fun d _ => map_zero _
  add_mem' := by
    intro a b ha hb d hd
    rw [map_add, ha d hd, hb d hd, add_zero]
  smul_mem' := by
    intro c θ hθ d hd
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hx2 : InBox N x.2 := fun i => lt_of_le_of_lt (by rw [← hx]; simp) (hd i)
    rw [hθ x.2 hx2, mul_zero]

def part (N : Fin g → ℕ) (θ : MvPowerSeries (Fin g) R) (i : Fin g) : MvPowerSeries (Fin g) R :=
  fun e => if (∀ j, j < i → e j < N j) then coeff (e + Finsupp.single i (N i)) θ else 0

def toFinsupp (u : (i : Fin g) → Fin (N i)) : Fin g →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (u i : ℕ)

def extend (v : ((i : Fin g) → Fin (N i)) → R) : MvPowerSeries (Fin g) R :=
  fun d => if h : InBox N d then v (fun i => ⟨d i, h i⟩) else 0

def extendLin (R : Type*) [CommRing R] (g : ℕ) (N : Fin g → ℕ) :
    (((i : Fin g) → Fin (N i)) → R) →ₗ[R] (MvPowerSeries (Fin g) R ⧸ powIdeal R g N) :=
  (Ideal.Quotient.mkₐ R (powIdeal R g N)).toLinearMap ∘ₗ
    { toFun := extend
      map_add' := fun v w => by
        refine MvPowerSeries.ext fun d => ?_
        rw [map_add, coeff_extend, coeff_extend, coeff_extend]
        split_ifs <;> simp
      map_smul' := fun c v => by
        refine MvPowerSeries.ext fun d => ?_
        rw [map_smul, coeff_extend, coeff_extend, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> simp }

def boxEquiv (R : Type*) [CommRing R] (g : ℕ) (N : Fin g → ℕ) :
    (((i : Fin g) → Fin (N i)) → R) ≃ₗ[R] (MvPowerSeries (Fin g) R ⧸ powIdeal R g N) :=
  LinearEquiv.ofBijective (extendLin R g N) ⟨extendLin_injective, extendLin_surjective⟩

end CerednikDrinfeld.BoxBasisLemma

end

end BoxBasisLemmaAppendix

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.LubinTate

namespace CerednikDrinfeld.Standard

universe u v

variable {p : ℕ} [Fact p.Prime]

open scoped CerednikDrinfeld_StandardFormalODModule

section Standard

def lawLin (i : Fin 2) : Fin 2 ⊕ Fin 2 → 𝕆 :=
  Sum.elim (fun j => if j = i then 1 else 0) (fun j => if j = i then 1 else 0)

variable (p)

def lawSeries (i : Fin 2) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝕆 := lt p (Fin 2 ⊕ Fin 2) (lawLin i)

variable {p}

def law : MvFormalGroup 2 𝕆 where
  toPowerSeries := lawSeries p
  constantCoeff_eq_zero := constantCoeff_lawSeries
  coeff_single_inl i j := by
    rw [coeff_single_lawSeries]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  coeff_single_inr i j := by
    rw [coeff_single_lawSeries]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  assoc i := by
def chi (i : Fin 2) : 𝕆 →+* 𝕆 := if i = 0 then RingHom.id _ else WittVector.frobenius

variable (p)

def actSeries (a : 𝕆) : Series 𝕆 := fun i => lt p (Fin 2) fun s => if s = i then chi i a else 0

def varpiLin (i s : Fin 2) : 𝕆 := if i = 0 then (if s = 1 then p else 0) else (if s = 0 then 1 else 0)

def varpiSeries : Series 𝕆 := fun i => lt p (Fin 2) (varpiLin p i)

variable {p}

def standard : FormalODModule p 𝕆 where
  F := law
  isComm := law_isComm
  act := actSeries p
  varpi := varpiSeries p
  isLawHom_act a := isLawHom_of_comm (constantCoeff_actSeries a) (comm_actSeries a)
  isLawHom_varpi := isLawHom_of_comm constantCoeff_varpiSeries comm_varpiSeries
  act_one := by
end Standard

section Identities

def emb (i : Fin 2) : Fin 1 ⊕ Fin 1 → Fin 2 ⊕ Fin 2 := Sum.map (fun _ => i) fun _ => i

end Identities

section OverB

variable {B : Type*} [CommRing B] [CharP B p] (j : Zp2 p →+* B)

def modB : FormalODModule p B := (standard (p := p)).map j

def lieZeroEquiv : ↥((modB j).lieZero j) ≃ₗ[B] B where
  toFun m := (m : Fin 2 → B) 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun b := ⟨Pi.single 0 b, (mem_lieZero_iff j _).mpr (by simp)⟩
  left_inv m := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simp
    · simpa using ((mem_lieZero_iff j _).mp m.2).symm
  right_inv b := by simp

def lieOneEquiv : ↥((modB j).lieOne j) ≃ₗ[B] B where
  toFun m := (m : Fin 2 → B) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun b := ⟨Pi.single 1 b, (mem_lieOne_iff j _).mpr (by simp)⟩
  left_inv m := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simpa using ((mem_lieOne_iff j _).mp m.2).symm
    · simp
  right_inv b := by simp

end OverB

def _root_.CerednikDrinfeld.SpecialFormalODModule.standard {B : Type u} [CommRing B] [CharP B p]
    (j : Zp2 p →+* B) : SpecialFormalODModule p j where
  toFormalODModule := modB j
  isSpecial := isSpecial j
  hasHeight := hasHeight j


section Biproduct

variable {B : Type u} [CommRing B] [CharP B p] (j : Zp2 p →+* B)

def single₂ {τ : Type*} (i : Fin 2) (x : MvPowerSeries τ B) : Fin 2 → MvPowerSeries τ B :=
  fun l => if l = i then x else 0

def incl (i : Fin 2) : MvFormalGroup.Hom (sigmaBar j) (modB j).F where
  toPowerSeries := single₂ i (X 0 : MvPowerSeries (Fin 1) B)
  constantCoeff_eq_zero := constantCoeff_single₂ i (constantCoeff_X 0)
  subst_eq l := by
    have hXl : HasSubst (fun l' : Fin 1 => (X (Sum.inl l') : MvPowerSeries (Fin 1 ⊕ Fin 1) B)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have hXr : HasSubst (fun l' : Fin 1 => (X (Sum.inr l') : MvPowerSeries (Fin 1 ⊕ Fin 1) B)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    rw [subst_single₂ i hXl, subst_single₂ i hXr, subst_X hXl, subst_X hXr,
      subst_elim_modB_F j (constantCoeff_single₂ i (constantCoeff_X _))
        (constantCoeff_single₂ i (constantCoeff_X _)), single₂_apply, single₂_apply, single₂_apply]
    split_ifs with h
    · rw [subst_X (sigmaBar j).hasSubst_toPowerSeries, sigmaBar_toPowerSeries]
      have hid : (Sum.elim (fun _ : Fin 1 => (X (Sum.inl 0) : MvPowerSeries (Fin 1 ⊕ Fin 1) B))
          fun _ : Fin 1 => (X (Sum.inr 0) : MvPowerSeries (Fin 1 ⊕ Fin 1) B))
          = fun s => X s := by
        funext s; rcases s with m | m <;> rw [Fin.fin_one_eq_zero m] <;> rfl
      rw [hid]
      exact (congrFun MvPowerSeries.subst_self _).symm
    · rw [← coe_substAlgHom (sigmaBar j).hasSubst_toPowerSeries, map_zero]
      have h00 : (Sum.elim (fun _ : Fin 1 => (0 : MvPowerSeries (Fin 1 ⊕ Fin 1) B))
          fun _ : Fin 1 => (0 : MvPowerSeries (Fin 1 ⊕ Fin 1) B)) = fun _ => 0 := by
        funext s; rcases s with m | m <;> rfl
      rw [h00]
      exact (MvFormalGroup.subst_zero_of_constantCoeff_eq_zero (constantCoeff_sigmaBarSeries j)).symm

def proj (i : Fin 2) : MvFormalGroup.Hom (modB j).F (sigmaBar j) where
  toPowerSeries := fun _ => (X i : MvPowerSeries (Fin 2) B)
  constantCoeff_eq_zero := fun _ => constantCoeff_X i
  subst_eq l := by
    have hXl : HasSubst (fun l' : Fin 2 => (X (Sum.inl l') : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have hXr : HasSubst (fun l' : Fin 2 => (X (Sum.inr l') : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    rw [subst_X (modB j).F.hasSubst_toPowerSeries, Fin.fin_one_eq_zero l, sigmaBar_toPowerSeries,
      modB_F_toPowerSeries]
    congr 1
    funext s
    rcases s with m | m
    · rw [Sum.elim_inl, subst_X hXl]; rfl
    · rw [Sum.elim_inr, subst_X hXr]; rfl

def cell (i i' : Fin 2) (e : MvFormalGroup.End (sigmaBar j)) : MvFormalGroup.End (modB j).F :=
  ((incl j i).comp e).comp (proj j i')

def entry (i i' : Fin 2) (E : MvFormalGroup.End (modB j).F) : MvFormalGroup.End (sigmaBar j) :=
  ((proj j i).comp E).comp (incl j i')

end Biproduct

end CerednikDrinfeld.Standard

end
