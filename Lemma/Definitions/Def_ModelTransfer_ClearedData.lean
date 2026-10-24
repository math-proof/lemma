import Lemma.Definitions.Def_FLTPrelim_Modularity
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

open WeierstrassCurve

namespace FLT.ModelTransfer

private lemma exists_intCast_eq_natCast_mul (x : ℚ) {N : ℕ} (hd : x.den ∣ N) :
    ∃ m : ℤ, (m : ℚ) = (N : ℚ) * x := by
  obtain ⟨k, hk⟩ := hd
  refine ⟨(k : ℤ) * x.num, ?_⟩
  have hden : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
  have hnum : x * (x.den : ℚ) = (x.num : ℚ) := (eq_div_iff hden).mp (Rat.num_div_den x).symm
  subst hk
  push_cast
  linear_combination (-(k : ℚ)) * hnum

structure ClearedData (C : VariableChange ℚ) where

  N : ℕ

  hN : N ≠ 0

  U : ℤ

  U' : ℤ

  R : ℤ

  S : ℤ

  T : ℤ

  hU : (U : ℚ) = (N : ℚ) * (C.u : ℚ)

  hU' : (U' : ℚ) = (N : ℚ) * ((C.u : ℚ))⁻¹

  hR : (R : ℚ) = (N : ℚ) * C.r

  hS : (S : ℚ) = (N : ℚ) * C.s

  hT : (T : ℚ) = (N : ℚ) * C.t

noncomputable def clearedData (C : VariableChange ℚ) : ClearedData C := by
  classical
  set d₁ : ℕ := (C.u : ℚ).den with hd₁
  set d₂ : ℕ := ((C.u : ℚ))⁻¹.den with hd₂
  set d₃ : ℕ := C.r.den with hd₃
  set d₄ : ℕ := C.s.den with hd₄
  set d₅ : ℕ := C.t.den with hd₅
  have hN : d₁ * d₂ * d₃ * d₄ * d₅ ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero
      (Nat.mul_ne_zero (C.u : ℚ).den_nz ((C.u : ℚ))⁻¹.den_nz) C.r.den_nz) C.s.den_nz)
      C.t.den_nz
  have hu : d₁ ∣ d₁ * d₂ * d₃ * d₄ * d₅ := ⟨d₂ * d₃ * d₄ * d₅, by ring⟩
  have hu' : d₂ ∣ d₁ * d₂ * d₃ * d₄ * d₅ := ⟨d₁ * d₃ * d₄ * d₅, by ring⟩
  have hr : d₃ ∣ d₁ * d₂ * d₃ * d₄ * d₅ := ⟨d₁ * d₂ * d₄ * d₅, by ring⟩
  have hs : d₄ ∣ d₁ * d₂ * d₃ * d₄ * d₅ := ⟨d₁ * d₂ * d₃ * d₅, by ring⟩
  have ht : d₅ ∣ d₁ * d₂ * d₃ * d₄ * d₅ := ⟨d₁ * d₂ * d₃ * d₄, by ring⟩
  exact
    { N := d₁ * d₂ * d₃ * d₄ * d₅
      hN := hN
      U := (exists_intCast_eq_natCast_mul _ hu).choose
      U' := (exists_intCast_eq_natCast_mul _ hu').choose
      R := (exists_intCast_eq_natCast_mul _ hr).choose
      S := (exists_intCast_eq_natCast_mul _ hs).choose
      T := (exists_intCast_eq_natCast_mul _ ht).choose
      hU := (exists_intCast_eq_natCast_mul _ hu).choose_spec
      hU' := (exists_intCast_eq_natCast_mul _ hu').choose_spec
      hR := (exists_intCast_eq_natCast_mul _ hr).choose_spec
      hS := (exists_intCast_eq_natCast_mul _ hs).choose_spec
      hT := (exists_intCast_eq_natCast_mul _ ht).choose_spec }

namespace ClearedData

variable {C : VariableChange ℚ} (D : ClearedData C)

lemma hNQ : ((D.N : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr D.hN

lemma huQ : ((C.u : ℚ)) ≠ 0 := C.u.ne_zero

lemma U_mul_U' : D.U * D.U' = (D.N : ℤ) ^ 2 := by
  have hu : ((C.u : ℚ)) ≠ 0 := C.u.ne_zero
  have key : ((D.U * D.U' : ℤ) : ℚ) = (((D.N : ℤ) ^ 2 : ℤ) : ℚ) := by
    push_cast
    rw [D.hU, D.hU']
    field_simp
  exact_mod_cast key

end ClearedData

section IntegerIdentities

variable {V W : WeierstrassCurve ℤ} {C : VariableChange ℚ}

private lemma ratId₁ (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ)) :
    (W.a₁ : ℚ) = ((C.u : ℚ))⁻¹ * ((V.a₁ : ℚ) + 2 * C.s) := by
  have h := congrArg WeierstrassCurve.a₁ hC
  simp only [variableChange_def, map_a₁, eq_intCast, Units.val_inv_eq_inv_val] at h
  exact h.symm

private lemma ratId₂ (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ)) :
    (W.a₂ : ℚ) = ((C.u : ℚ))⁻¹ ^ 2 *
      ((V.a₂ : ℚ) - C.s * (V.a₁ : ℚ) + 3 * C.r - C.s ^ 2) := by
  have h := congrArg WeierstrassCurve.a₂ hC
  simp only [variableChange_def, map_a₁, map_a₂, eq_intCast, Units.val_inv_eq_inv_val] at h
  exact h.symm

private lemma ratId₃ (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ)) :
    (W.a₃ : ℚ) = ((C.u : ℚ))⁻¹ ^ 3 *
      ((V.a₃ : ℚ) + C.r * (V.a₁ : ℚ) + 2 * C.t) := by
  have h := congrArg WeierstrassCurve.a₃ hC
  simp only [variableChange_def, map_a₁, map_a₃, eq_intCast, Units.val_inv_eq_inv_val] at h
  exact h.symm

private lemma ratId₄ (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ)) :
    (W.a₄ : ℚ) = ((C.u : ℚ))⁻¹ ^ 4 *
      ((V.a₄ : ℚ) - C.s * (V.a₃ : ℚ) + 2 * C.r * (V.a₂ : ℚ)
        - (C.t + C.r * C.s) * (V.a₁ : ℚ) + 3 * C.r ^ 2 - 2 * C.s * C.t) := by
  have h := congrArg WeierstrassCurve.a₄ hC
  simp only [variableChange_def, map_a₁, map_a₂, map_a₃, map_a₄, eq_intCast,
    Units.val_inv_eq_inv_val] at h
  exact h.symm

private lemma ratId₆ (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ)) :
    (W.a₆ : ℚ) = ((C.u : ℚ))⁻¹ ^ 6 *
      ((V.a₆ : ℚ) + C.r * (V.a₄ : ℚ) + C.r ^ 2 * (V.a₂ : ℚ) + C.r ^ 3
        - C.t * (V.a₃ : ℚ) - C.t ^ 2 - C.r * C.t * (V.a₁ : ℚ)) := by
  have h := congrArg WeierstrassCurve.a₆ hC
  simp only [variableChange_def, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, eq_intCast,
    Units.val_inv_eq_inv_val] at h
  exact h.symm

lemma intId₁ (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (D : ClearedData C) :
    (D.N : ℤ) ^ 2 * W.a₁ = D.U' * ((D.N : ℤ) * V.a₁ + 2 * D.S) := by
  have h := ratId₁ hC
  have hu : ((C.u : ℚ)) ≠ 0 := C.u.ne_zero
  have key : (((D.N : ℤ) ^ 2 * W.a₁ : ℤ) : ℚ)
      = ((D.U' * ((D.N : ℤ) * V.a₁ + 2 * D.S) : ℤ) : ℚ) := by
    push_cast
    rw [h, D.hU', D.hS]
    field_simp
  exact_mod_cast key

lemma intId₂ (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (D : ClearedData C) :
    (D.N : ℤ) ^ 4 * W.a₂
      = D.U' ^ 2 * ((D.N : ℤ) ^ 2 * V.a₂ - D.S * (D.N : ℤ) * V.a₁
        + 3 * (D.N : ℤ) * D.R - D.S ^ 2) := by
  have h := ratId₂ hC
  have hu : ((C.u : ℚ)) ≠ 0 := C.u.ne_zero
  have key : (((D.N : ℤ) ^ 4 * W.a₂ : ℤ) : ℚ)
      = ((D.U' ^ 2 * ((D.N : ℤ) ^ 2 * V.a₂ - D.S * (D.N : ℤ) * V.a₁
          + 3 * (D.N : ℤ) * D.R - D.S ^ 2) : ℤ) : ℚ) := by
    push_cast
    rw [h, D.hU', D.hS, D.hR]
    field_simp
  exact_mod_cast key

lemma intId₃ (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (D : ClearedData C) :
    (D.N : ℤ) ^ 4 * W.a₃
      = D.U' ^ 3 * ((D.N : ℤ) * V.a₃ + D.R * V.a₁ + 2 * D.T) := by
  have h := ratId₃ hC
  have hu : ((C.u : ℚ)) ≠ 0 := C.u.ne_zero
  have key : (((D.N : ℤ) ^ 4 * W.a₃ : ℤ) : ℚ)
      = ((D.U' ^ 3 * ((D.N : ℤ) * V.a₃ + D.R * V.a₁ + 2 * D.T) : ℤ) : ℚ) := by
    push_cast
    rw [h, D.hU', D.hR, D.hT]
    field_simp
  exact_mod_cast key

lemma intId₄ (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (D : ClearedData C) :
    (D.N : ℤ) ^ 6 * W.a₄
      = D.U' ^ 4 * ((D.N : ℤ) ^ 2 * V.a₄ - D.S * (D.N : ℤ) * V.a₃
        + 2 * D.R * (D.N : ℤ) * V.a₂ - (D.T * (D.N : ℤ) + D.R * D.S) * V.a₁
        + 3 * D.R ^ 2 - 2 * D.S * D.T) := by
  have h := ratId₄ hC
  have hu : ((C.u : ℚ)) ≠ 0 := C.u.ne_zero
  have key : (((D.N : ℤ) ^ 6 * W.a₄ : ℤ) : ℚ)
      = ((D.U' ^ 4 * ((D.N : ℤ) ^ 2 * V.a₄ - D.S * (D.N : ℤ) * V.a₃
          + 2 * D.R * (D.N : ℤ) * V.a₂ - (D.T * (D.N : ℤ) + D.R * D.S) * V.a₁
          + 3 * D.R ^ 2 - 2 * D.S * D.T) : ℤ) : ℚ) := by
    push_cast
    rw [h, D.hU', D.hS, D.hR, D.hT]
    field_simp
  exact_mod_cast key

lemma intId₆ (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (D : ClearedData C) :
    (D.N : ℤ) ^ 9 * W.a₆
      = D.U' ^ 6 * ((D.N : ℤ) ^ 3 * V.a₆ + D.R * (D.N : ℤ) ^ 2 * V.a₄
        + D.R ^ 2 * (D.N : ℤ) * V.a₂ + D.R ^ 3 - D.T * (D.N : ℤ) ^ 2 * V.a₃
        - D.T ^ 2 * (D.N : ℤ) - D.R * D.T * (D.N : ℤ) * V.a₁) := by
  have h := ratId₆ hC
  have hu : ((C.u : ℚ)) ≠ 0 := C.u.ne_zero
  have key : (((D.N : ℤ) ^ 9 * W.a₆ : ℤ) : ℚ)
      = ((D.U' ^ 6 * ((D.N : ℤ) ^ 3 * V.a₆ + D.R * (D.N : ℤ) ^ 2 * V.a₄
          + D.R ^ 2 * (D.N : ℤ) * V.a₂ + D.R ^ 3 - D.T * (D.N : ℤ) ^ 2 * V.a₃
          - D.T ^ 2 * (D.N : ℤ) - D.R * D.T * (D.N : ℤ) * V.a₁) : ℤ) : ℚ) := by
    push_cast
    rw [h, D.hU', D.hR, D.hT]
    field_simp
  exact_mod_cast key

end IntegerIdentities

section Reduction

variable {C : VariableChange ℚ} (D : ClearedData C)
variable {q : ℕ} [Fact q.Prime]

lemma N_ne_zero_zmod (hq : ¬ q ∣ D.N) : ((D.N : ZMod q)) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact hq

lemma U_ne_zero_zmod (hq : ¬ q ∣ D.N) : ((D.U : ZMod q)) ≠ 0 := by
  intro h
  have h2 : ((D.U * D.U' : ℤ) : ZMod q) = 0 := by push_cast; rw [h]; ring
  rw [D.U_mul_U'] at h2
  push_cast at h2
  rw [pow_two, mul_self_eq_zero] at h2
  exact N_ne_zero_zmod D hq h2

lemma U'_ne_zero_zmod (hq : ¬ q ∣ D.N) : ((D.U' : ZMod q)) ≠ 0 := by
  intro h
  have h2 : ((D.U * D.U' : ℤ) : ZMod q) = 0 := by push_cast; rw [h]; ring
  rw [D.U_mul_U'] at h2
  push_cast at h2
  rw [pow_two, mul_self_eq_zero] at h2
  exact N_ne_zero_zmod D hq h2

lemma U_mul_U'_zmod : ((D.U : ZMod q)) * ((D.U' : ZMod q)) = ((D.N : ZMod q)) ^ 2 := by
  have h := congrArg (fun m : ℤ => ((m : ZMod q))) D.U_mul_U'
  push_cast at h
  exact_mod_cast h

noncomputable def reducedUnit (hq : ¬ q ∣ D.N) : (ZMod q)ˣ where
  val := ((D.U : ZMod q)) * ((D.N : ZMod q))⁻¹
  inv := ((D.U' : ZMod q)) * ((D.N : ZMod q))⁻¹
  val_inv := by
    have hN := N_ne_zero_zmod D hq
    have hUU' := U_mul_U'_zmod (q := q) D
    field_simp [hN]
    linear_combination hUU'
  inv_val := by
    have hN := N_ne_zero_zmod D hq
    have hUU' := U_mul_U'_zmod (q := q) D
    field_simp [hN]
    linear_combination hUU'

noncomputable def reducedChange (hq : ¬ q ∣ D.N) : VariableChange (ZMod q) where
  u := reducedUnit D hq
  r := ((D.R : ZMod q)) * ((D.N : ZMod q))⁻¹
  s := ((D.S : ZMod q)) * ((D.N : ZMod q))⁻¹
  t := ((D.T : ZMod q)) * ((D.N : ZMod q))⁻¹

variable (hq : ¬ q ∣ D.N)

@[simp] lemma reducedChange_u_inv :
    ((((reducedChange D hq).u)⁻¹ : (ZMod q)ˣ) : ZMod q)
      = ((D.U' : ZMod q)) * ((D.N : ZMod q))⁻¹ := rfl

@[simp] lemma reducedChange_u :
    ((((reducedChange D hq).u) : (ZMod q)ˣ) : ZMod q)
      = ((D.U : ZMod q)) * ((D.N : ZMod q))⁻¹ := rfl

@[simp] lemma reducedChange_r :
    (reducedChange D hq).r = ((D.R : ZMod q)) * ((D.N : ZMod q))⁻¹ := rfl

@[simp] lemma reducedChange_s :
    (reducedChange D hq).s = ((D.S : ZMod q)) * ((D.N : ZMod q))⁻¹ := rfl

@[simp] lemma reducedChange_t :
    (reducedChange D hq).t = ((D.T : ZMod q)) * ((D.N : ZMod q))⁻¹ := rfl

end Reduction

end FLT.ModelTransfer
