import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.QuantumInformation.Finite.TsirelsonTight
open Matrix
open MathlibExt.QuantumInformation.Finite.TsirelsonTight


namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[sqrt2_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma sqrt2_pos : 0 < Real.sqrt 2 :=
  Real.sqrt_pos.mpr (by norm_num)

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[sqrt2_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma sqrt2_ne : Real.sqrt 2 ≠ 0 :=
  ne_of_gt sqrt2_pos

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[sqrt2_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma sqrt2_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rwa [pow_two] at h

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[s_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma s_ne_zero : s ≠ 0 := by
  unfold s
  intro h
  have h' : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (((0 : ℝ)) : ℂ)) := by
    rw [h, Complex.ofReal_zero]
  have h2 : (Real.sqrt 2)⁻¹ = 0 := Complex.ofReal_inj.mp h'
  exact inv_ne_zero sqrt2_ne h2

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[u_mul_s](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma u_mul_s : u * s = 1 := by
  unfold u s
  rw [← Complex.ofReal_mul]
  have h : Real.sqrt 2 * (Real.sqrt 2)⁻¹ = 1 := mul_inv_cancel₀ sqrt2_ne
  rw [h, Complex.ofReal_one]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[u_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma u_mul_self : u * u = 2 := by
  unfold u
  rw [← Complex.ofReal_mul, sqrt2_mul_self]
  simp

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[s_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma s_mul_self : s * s = 1 / 2 := by
  unfold s
  rw [← Complex.ofReal_mul]
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 2⁻¹ := by
    rw [← mul_inv, sqrt2_mul_self]
  rw [h, Complex.ofReal_inv]
  have h2 : (((2 : ℝ)) : ℂ) = 2 := by simp
  rw [h2, div_eq_mul_inv, one_mul]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[s_star](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma s_star : star s = s := by
  unfold s
  simp

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[A₀_inv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma A₀_inv : A₀ ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, A₀]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[A₁_inv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma A₁_inv : A₁ ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, A₁]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[B₀_inv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma B₀_inv : B₀ ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, B₀] <;>
    linear_combination 2 * s_mul_self

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[B₁_inv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma B₁_inv : B₁ ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, B₁] <;>
    linear_combination 2 * s_mul_self

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[A₀_sa](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma A₀_sa : star A₀ = A₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply, A₀]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[A₁_sa](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma A₁_sa : star A₁ = A₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply, A₁]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[B₀_sa](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma B₀_sa : star B₀ = B₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply, B₀]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[B₁_sa](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma B₁_sa : star B₁ = B₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply, B₁]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[A₀B₀_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma A₀B₀_comm : A₀ * B₀ = B₀ * A₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, A₀, B₀]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[A₀B₁_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma A₀B₁_comm : A₀ * B₁ = B₁ * A₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, A₀, B₁]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[A₁B₀_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma A₁B₀_comm : A₁ * B₀ = B₀ * A₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, A₁, B₀]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[A₁B₁_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma A₁B₁_comm : A₁ * B₁ = B₁ * A₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, A₁, B₁]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[B₀_mulVec_v](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma B₀_mulVec_v : B₀ *ᵥ v = ![1 / 2, 1 / 2, 1 / 2, -1 / 2] := by
  ext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, B₀, v, s_mul_self, neg_div]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[B₁_mulVec_v](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma B₁_mulVec_v : B₁ *ᵥ v = ![1 / 2, -1 / 2, -1 / 2, -1 / 2] := by
  ext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, B₁, v, s_mul_self, neg_div]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[A₀B₀_mulVec_v](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma A₀B₀_mulVec_v : (A₀ * B₀) *ᵥ v = ![1 / 2, 1 / 2, -1 / 2, 1 / 2] := by
  rw [← Matrix.mulVec_mulVec, B₀_mulVec_v]
  ext k
  fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, A₀] <;> ring

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[A₀B₁_mulVec_v](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma A₀B₁_mulVec_v : (A₀ * B₁) *ᵥ v = ![1 / 2, -1 / 2, 1 / 2, 1 / 2] := by
  rw [← Matrix.mulVec_mulVec, B₁_mulVec_v]
  ext k
  fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, A₀] <;> ring

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[A₁B₀_mulVec_v](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma A₁B₀_mulVec_v : (A₁ * B₀) *ᵥ v = ![1 / 2, -1 / 2, 1 / 2, 1 / 2] := by
  rw [← Matrix.mulVec_mulVec, B₀_mulVec_v]
  ext k
  fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, A₁]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[A₁B₁_mulVec_v](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma A₁B₁_mulVec_v : (A₁ * B₁) *ᵥ v = ![-1 / 2, -1 / 2, 1 / 2, -1 / 2] := by
  rw [← Matrix.mulVec_mulVec, B₁_mulVec_v]
  ext k
  fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, A₁]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[chsh_mulVec_v](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma chsh_mulVec_v :
  (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) *ᵥ v = ![2, 0, 0, 2] := by
  have hAdd : (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) *ᵥ v =
    ((A₀ * B₀) *ᵥ v + (A₀ * B₁) *ᵥ v + (A₁ * B₀) *ᵥ v - (A₁ * B₁) *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.add_mulVec]
  rw [hAdd, A₀B₀_mulVec_v, A₀B₁_mulVec_v, A₁B₀_mulVec_v, A₁B₁_mulVec_v]
  ext k
  fin_cases k <;> simp <;> ring

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[v_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma v_ne_zero : v ≠ 0 := by
  intro h
  have h0 : v 0 = (0 : Fin 4 → ℂ) 0 := by rw [h]
  simp [v, s_ne_zero] at h0

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[mu_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma mu_eq : ((↑(2 * Real.sqrt 2) : ℂ)) = 2 * u := by
  unfold u
  rw [Complex.ofReal_mul]
  simp

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[mu_mul_s](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma mu_mul_s : ((↑(2 * Real.sqrt 2) : ℂ)) * s = 2 := by
  rw [mu_eq, mul_assoc, u_mul_s, mul_one]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[mu_smul_s](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma mu_smul_s : ((↑(2 * Real.sqrt 2) : ℂ)) • s = 2 := by
  rwa [smul_eq_mul]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[two_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
private lemma two_eq : (2 : ℂ) = 2 * ((Real.sqrt 2 : ℝ) : ℂ) * s := by
  have h := mu_mul_s
  push_cast at h
  exact h.symm

end MathlibExt.QuantumInformation.Finite.TsirelsonTight

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

/--
[tsirelson_bound_tight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean)
-/
@[path]
lemma tsirelson_bound_tight
  :
-- imply
  ∃ (A₀ A₁ B₀ B₁ : Matrix (Fin 4) (Fin 4) ℂ),
    IsCHSHTuple A₀ A₁ B₀ B₁ ∧
    Module.End.HasEigenvalue
    (Matrix.toLin' (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁))
    ((↑(2 * Real.sqrt 2) : ℂ)) := by
-- proof
  refine ⟨A₀, A₁, B₀, B₁,
    ⟨A₀_inv, A₁_inv, B₀_inv, B₁_inv, A₀_sa, A₁_sa, B₀_sa, B₁_sa,
      A₀B₀_comm, A₀B₁_comm, A₁B₀_comm, A₁B₁_comm⟩, ?_⟩
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
  refine ⟨?_, v_ne_zero⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, chsh_mulVec_v]
  ext k
  fin_cases k <;> simp [v, mu_mul_s, smul_eq_mul, -Complex.ofReal_mul]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight


-- created on 2026-10-20
-- updated on 2026-10-26
