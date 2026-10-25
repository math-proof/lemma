import Mathlib
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Abbrev.LocalGL2_Kirillov
import Notation.LocalGL2_Kirillov

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open scoped Classical

noncomputable section

namespace LocalGL2.Kirillov

open AutomorphicForm IsDedekindDomain NumberField

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open scoped LocalGL2_Kirillov

def defectSet (ψ : AddChar F ℂ) (S : Submodule ℂ (G → ℂ)) : Set (G → ℂ) :=
  {V | ∃ U ∈ S, ∃ x : F, V = (fun g => U (g * unipotentGL2 x)) - ψ x • U}

abbrev defectSpan (ψ : AddChar F ℂ) (S : Submodule ℂ (G → ℂ)) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (defectSet v ψ S)

def rT (k : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun V := fun g => V (g * k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev coinv (ψ : AddChar F ℂ) (S : Submodule ℂ (G → ℂ)) : Submodule ℂ ((G → ℂ) ⧸ defectSpan v ψ S) :=
  S.map (defectSpan v ψ S).mkQ

def dg (a : Fx) : G where
  val := !![(a : F), 0; 0, 1]
  inv := !![((a⁻¹ : Fx) : F), 0; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def wG : G where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def zG (c : Fx) : G where
  val := !![(c : F), 0; 0, (c : F)]
  inv := !![((c⁻¹ : Fx) : F), 0; 0, ((c⁻¹ : Fx) : F)]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def UF : Subgroup Fx where
  carrier := {u | Valued.v (u : F) = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at ha hb ⊢
    rw [ha, hb, mul_one]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
    rw [ha, inv_one]

def Um (δ : Γ) : Subgroup (UF v) where
  carrier := {u | Valued.v (((u : Fx) : F) - 1) < (δ : WithZero (Multiplicative ℤ))}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have e : (((a * b : UF v) : Fx) : F) - 1 = ((a : Fx) : F) * (((b : Fx) : F) - 1) + (((a : Fx) : F) - 1) := by
      simp only [Subgroup.coe_mul, Units.val_mul]
      ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ha)
    rw [map_mul, v_coe_UF, one_mul]
    exact hb
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have e : (((a⁻¹ : UF v) : Fx) : F) - 1 = (((a⁻¹ : UF v) : Fx) : F) * (1 - ((a : Fx) : F)) := by
      have h : (((a⁻¹ : UF v) : Fx) : F) * ((a : Fx) : F) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
      rw [mul_sub, mul_one, h]
    rw [e, map_mul, v_coe_UF, one_mul, Valuation.map_sub_swap]
    exact ha

abbrev Qm (δ : Γ) : Type := UF v ⧸ Um v δ

def rep (δ : Γ) (q : Qm v δ) : UF v := q.out

section charGeneric

variable {A : Type*} [AddCommGroup A]

end charGeneric

def Ch (δ : Γ) : Type := AddChar (Additive (Qm v δ)) ℂ

variable {v} in

def Ch.toChar {δ : Γ} (χ : Ch v δ) : AddChar (Additive (Qm v δ)) ℂ := χ

variable {v} in

def chv {δ : Γ} (χ : Ch v δ) (u : UF v) : ℂ := Ch.toChar χ (Additive.ofMul (u : Qm v δ))

section fourier

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

def IsLvl (δ : Γ) (f : UF v → X) : Prop := ∀ u : UF v, ∀ m ∈ Um v δ, f (u * m) = f u

def comp (δ : Γ) (f : UF v → X) (χ : Ch v δ) : X :=
  (Fintype.card (Qm v δ) : ℂ)⁻¹ • ∑ q : Qm v δ, chv χ (rep v δ q) • f (rep v δ q)

def chOfFun (δ : Γ) (f : UF v → ℂ) (hmul : ∀ u w : UF v, f (u * w) = f u * f w)
    (htriv : ∀ m ∈ Um v δ, f m = 1) : Ch v δ where
  toFun a := f (rep v δ (Additive.toMul a))
  map_zero_eq_one' := by
    show f (rep v δ (1 : Qm v δ)) = 1
    apply htriv
    rw [← QuotientGroup.eq_one_iff, mk_rep]
  map_add_eq_mul' a b := by
    show f (rep v δ (Additive.toMul a * Additive.toMul b)) =
      f (rep v δ (Additive.toMul a)) * f (rep v δ (Additive.toMul b))
    rw [← hmul]
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Um v δ)
      (rep v δ (Additive.toMul a) * rep v δ (Additive.toMul b))
    have hclass : rep v δ (Additive.toMul a * Additive.toMul b) =
        ((rep v δ (Additive.toMul a) * rep v δ (Additive.toMul b) : UF v) : Qm v δ).out := by
      unfold rep
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']
    rw [hclass, hm, hmul, htriv m m.2, mul_one]

def refineCh {δ δ₁ : Γ} (h : δ ≤ δ₁) (τ : Ch v δ₁) : Ch v δ :=
  chOfFun v δ (chv τ) (chv_mul τ) fun _ hm => chv_of_mem τ (Um_mono v h hm)

def qmap {δ' δ : Γ} (h : δ' ≤ δ) : Qm v δ' →* Qm v δ :=
  QuotientGroup.map (Um v δ') (Um v δ) (MonoidHom.id (UF v)) fun _ hm => Um_mono v h hm

end fourier

section kirillovFunction

variable (ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ)
  (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ))

def kirillov (V : G → ℂ) (a : Fx) : (G → ℂ) ⧸ defectSpan v ψ S :=
  (defectSpan v ψ S).mkQ (rT v (dg v a) V)

def theta (V : G → ℂ) : (G → ℂ) ⧸ defectSpan v ψ S :=
  (defectSpan v ψ S).mkQ (rT v (wG v) V)

variable (ϖ : (HeightOneSpectrum.adicCompletion K v)ˣ)

def shell (V : G → ℂ) (n : ℤ) (u : UF v) : (G → ℂ) ⧸ defectSpan v ψ S :=
  kirillov v ψ S V (ϖ ^ n * (u : Fx))

def mel (δ : Γ) (V : G → ℂ) (n : ℤ) (χ : Ch v δ) : (G → ℂ) ⧸ defectSpan v ψ S :=
  comp v δ (shell v ψ S ϖ V n) χ

def IsBump {δ : Γ} (n : ℤ) (τ : Ch v δ) (ξ : (G → ℂ) ⧸ defectSpan v ψ S) (E : G → ℂ) : Prop :=
  ∀ (k : ℤ) (u : UF v), shell v ψ S ϖ E k u = if k = n then chv τ u • ξ else 0

end kirillovFunction

section uniformiser

variable (ϖ : (HeightOneSpectrum.adicCompletion K v)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion K v) = WithZero.exp (-1 : ℤ))

def lvl (K₀ : ℤ) : Γ := Units.mk0 (WithZero.exp K₀) WithZero.exp_ne_zero

def negUF : UF v := ⟨-1, by
  show Valued.v (((-1 : Fx) : F)) = 1
  rw [Units.val_neg, Units.val_one, Valuation.map_neg, Valuation.map_one]⟩

end uniformiser

end LocalGL2.Kirillov

end
