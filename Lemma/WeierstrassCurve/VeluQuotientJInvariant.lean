import Mathlib
import Lemma.WeierstrassCurve.VeluQuotientMap
import Instance.WeierstrassCurve_VeluQuotientJInvariant
import Def.WeierstrassCurve_VeluQuotientJInvariant

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (S : Finset (R × R))

lemma veluQuotient_c₄' : (W.veluQuotient S).c₄ = W.c₄ + 240 * W.veluTSum S := by
  simp only [c₄, veluQuotient_b₂, veluQuotient_b₄]
  ring

lemma veluQuotient_c₆ :
    (W.veluQuotient S).c₆ = W.c₆ + 504 * W.b₂ * W.veluTSum S + 6048 * W.veluWSum S := by
  simp only [c₆, veluQuotient_b₂, veluQuotient_b₄, veluQuotient_b₆]
  ring

theorem Δ_mul_j (V : WeierstrassCurve R) [V.IsElliptic] : V.Δ * V.j = V.c₄ ^ 3 := by
  rw [j, ← coe_Δ', ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

theorem veluQuotient_Δ_mul_j [(W.veluQuotient S).IsElliptic] :
    (W.veluQuotient S).Δ * (W.veluQuotient S).j = (W.c₄ + 240 * W.veluTSum S) ^ 3 := by
  rw [Δ_mul_j, veluQuotient_c₄']

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F))

theorem veluQuotient_j (hΔ : (W.veluQuotient S).Δ ≠ 0) :
    haveI : (W.veluQuotient S).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (W.veluQuotient S).j = (W.c₄ + 240 * W.veluTSum S) ^ 3 / (W.veluQuotient S).Δ := by
  haveI : (W.veluQuotient S).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  rw [eq_div_iff hΔ, mul_comm]
  exact veluQuotient_Δ_mul_j W S

theorem veluQuotient_j_mul_Δ_of_ne_zero (hΔ : (W.veluQuotient S).Δ ≠ 0) :
    haveI : (W.veluQuotient S).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (W.veluQuotient S).j * (W.veluQuotient S).Δ = (W.c₄ + 240 * W.veluTSum S) ^ 3 := by
  haveI : (W.veluQuotient S).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  rw [mul_comm]; exact veluQuotient_Δ_mul_j W S

end Field

namespace VeluQuotientJGates


example : W27a3.toAffine.Equation 0 0 := by
  rw [Affine.equation_iff]; simp [W27a3]

lemma veluTSum_S₀ : W27a3.veluTSum S₀ = 0 := by
  simp [W27a3, S₀, veluTSum, veluT_eq, b₂, b₄]

lemma veluWSum_S₀ : W27a3.veluWSum S₀ = 1 := by
  simp [W27a3, S₀, veluWSum, veluW, veluU, veluGy, veluT_eq, b₂, b₄]

theorem veluQuotient_27a3_eq : W27a3.veluQuotient S₀ = ⟨0, 0, 1, 0, -7⟩ := by
  ext <;>
    simp only [veluQuotient_a₁, veluQuotient_a₂, veluQuotient_a₃, veluQuotient_a₄,
      veluQuotient_a₆, veluTSum_S₀, veluWSum_S₀] <;>
    simp [W27a3, b₂]

theorem c₄_veluQuotient_27a3 : (W27a3.veluQuotient S₀).c₄ = 0 := by
  rw [veluQuotient_c₄', veluTSum_S₀]
  simp [W27a3, c₄, b₂, b₄]

theorem c₆_veluQuotient_27a3 : (W27a3.veluQuotient S₀).c₆ = 5832 := by
  rw [veluQuotient_c₆, veluTSum_S₀, veluWSum_S₀]
  simp only [W27a3, c₆, b₂, b₄, b₆]
  norm_num

theorem Δ_veluQuotient_27a3 : (W27a3.veluQuotient S₀).Δ = -19683 := by
  rw [veluQuotient_Δ, veluTSum_S₀, veluWSum_S₀]
  simp only [W27a3, Δ, b₂, b₄, b₆, b₈]
  norm_num

theorem j_veluQuotient_27a3 : (W27a3.veluQuotient S₀).j = 0 := by
  have hΔ : (W27a3.veluQuotient S₀).Δ ≠ 0 := by rw [Δ_veluQuotient_27a3]; norm_num
  rw [veluQuotient_j W27a3 S₀ hΔ, veluTSum_S₀]
  simp [W27a3, c₄, b₂, b₄]

example : (1728 : ℚ) * (-19683) = (0 : ℚ) ^ 3 - (5832 : ℚ) ^ 2 := by norm_num

example : S₀.Nonempty := ⟨(0, 0), Finset.mem_singleton_self _⟩

end VeluQuotientJGates

end WeierstrassCurve
