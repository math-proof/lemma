import Lemma.Definitions.Def_WeierstrassCurve_Velu
import Lemma.Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]

section Embedding

variable (C : VariableChange K)

def vcInvEmbedding : K × K ↪ K × K where
  toFun P := (Affine.vcXInv C P.1, Affine.vcYInv C P.1 P.2)
  inj' := by
    intro P P' h
    have h1 : Affine.vcXInv C P.1 = Affine.vcXInv C P'.1 := congrArg Prod.fst h
    have h2 : Affine.vcYInv C P.1 P.2 = Affine.vcYInv C P'.1 P'.2 := congrArg Prod.snd h
    have hx : P.1 = P'.1 := by
      have := congrArg (Affine.vcX C) h1
      simpa only [Affine.vcX_vcXInv] using this
    have hy : P.2 = P'.2 := by
      have := congrArg (Affine.vcY C (Affine.vcXInv C P.1)) h2
      rw [Affine.vcY_vcYInv, hx] at this
      simpa only [Affine.vcY_vcYInv] using this
    exact Prod.ext hx hy

@[simp] lemma vcInvEmbedding_apply (P : K × K) :
    vcInvEmbedding C P = (Affine.vcXInv C P.1, Affine.vcYInv C P.1 P.2) := rfl

end Embedding

section PerPoint

variable (C : VariableChange K) (W : WeierstrassCurve K)

lemma variableChange_veluGy (x y : K) :
    (C • W).veluGy (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 3 * W.veluGy x y := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma variableChange_veluGx (x y : K) :
    (C • W).veluGx (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 4 * (W.veluGx x y + C.s * W.veluGy x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluGx, veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁,
    variableChange_a₂, variableChange_a₄, Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma variableChange_veluT (x y : K) :
    (C • W).veluT (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 4 * W.veluT x y := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluT, veluGx, veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁,
    variableChange_a₂, variableChange_a₃, variableChange_a₄, Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma variableChange_veluU (x y : K) :
    (C • W).veluU (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 6 * W.veluU x y := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluU, veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma variableChange_veluW (x y : K) :
    (C • W).veluW (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 6 * (W.veluW x y - C.r * W.veluT x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluW, veluU, veluT, veluGx, veluGy, Affine.vcXInv, Affine.vcYInv,
    variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

end PerPoint

section Sums

variable (C : VariableChange K) (W : WeierstrassCurve K) (S : Finset (K × K))

lemma variableChange_veluTSum :
    (C • W).veluTSum (S.map (vcInvEmbedding C))
      = ((C.u⁻¹ : Kˣ) : K) ^ 4 * W.veluTSum S := by
  rw [veluTSum, veluTSum, Finset.sum_map, Finset.mul_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simpa only [vcInvEmbedding_apply] using variableChange_veluT C W P.1 P.2

lemma variableChange_veluWSum :
    (C • W).veluWSum (S.map (vcInvEmbedding C))
      = ((C.u⁻¹ : Kˣ) : K) ^ 6 * (W.veluWSum S - C.r * W.veluTSum S) := by
  rw [veluWSum, Finset.sum_map]
  rw [show W.veluWSum S - C.r * W.veluTSum S
      = ∑ P ∈ S, (W.veluW P.1 P.2 - C.r * W.veluT P.1 P.2) by
    rw [veluWSum, veluTSum, Finset.mul_sum, ← Finset.sum_sub_distrib]]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simpa only [vcInvEmbedding_apply] using variableChange_veluW C W P.1 P.2

end Sums

end WeierstrassCurve
