import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM12.NullFrameDecomposition
open Matrix NullFrame


namespace NullFrame

/--
[minkowskiInner_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean)
-/
@[path]
lemma minkowskiInner_comm
  {n : ℕ}
  {X Y : Fin (n + 1) → ℝ} :
-- imply
  minkowskiInner n X Y = minkowskiInner n Y X := by
-- proof
  simp only [minkowskiInner, minkowskiMetric, dotProduct, mulVec, of_apply]
  simp [mul_comm]

end NullFrame

namespace NullFrame

/--
[nullFrame_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean)
-/
@[path]
lemma nullFrame_decomposition
  {n : ℕ}
  {nf : NullFrameData n}
  {X Y : Fin (n + 1) → ℝ} :
-- imply
  minkowskiInner n X Y = -(1 / 2) * minkowskiInner n nf.L X * minkowskiInner n nf.Lb Y - (1 / 2) * minkowskiInner n nf.Lb X * minkowskiInner n nf.L Y + angularMetric n nf X Y := by
-- proof
  conv_lhs => rw [nf.completeness X]
  simp only [minkowskiInner, angularMetric]
  rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct]
  rw [sum_dotProduct (Finset.univ)
    (fun i => (dotProduct (nf.e i) (minkowskiMetric n *ᵥ X)) • nf.e i)]
  simp only [smul_dotProduct, smul_eq_mul]
  ring

end NullFrame

namespace NullFrame

/--
[angularMetric_vanish_L](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean)
-/
@[path]
lemma angularMetric_vanish_L
  {n : ℕ}
  {nf : NullFrameData n}
  {Y : Fin (n + 1) → ℝ} :
-- imply
  angularMetric n nf nf.L Y = 0 := by
-- proof
  simp only [angularMetric]
  apply Finset.sum_eq_zero
  intro i _
  have h : minkowskiInner n (nf.e i) nf.L = 0 := by
    rw [minkowskiInner_comm]; exact nf.L_e_orthog i
  simp [h]

end NullFrame

namespace NullFrame

/--
[angularMetric_vanish_Lb](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean)
-/
@[path]
lemma angularMetric_vanish_Lb
  {n : ℕ}
  {nf : NullFrameData n}
  {Y : Fin (n + 1) → ℝ} :
-- imply
  angularMetric n nf nf.Lb Y = 0 := by
-- proof
  simp only [angularMetric]
  apply Finset.sum_eq_zero
  intro i _
  have h : minkowskiInner n (nf.e i) nf.Lb = 0 := by
    rw [minkowskiInner_comm]; exact nf.Lb_e_orthog i
  simp [h]

end NullFrame

namespace NullFrame

/--
[angularMetric_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean)
-/
@[path]
lemma angularMetric_comm
  {n : ℕ}
  {nf : NullFrameData n}
  {X Y : Fin (n + 1) → ℝ} :
-- imply
  angularMetric n nf X Y = angularMetric n nf Y X := by
-- proof
  simp only [angularMetric]
  congr 1; ext i; ring

end NullFrame

namespace NullFrame

/--
[angularMetric_vanish_L_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean)
-/
@[path]
lemma angularMetric_vanish_L_right
  {n : ℕ}
  {nf : NullFrameData n}
  {X : Fin (n + 1) → ℝ} :
-- imply
  angularMetric n nf X nf.L = 0 := by
-- proof
  rw [angularMetric_comm]; exact angularMetric_vanish_L nf X

end NullFrame

namespace NullFrame

/--
[angularMetric_vanish_Lb_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean)
-/
@[path]
lemma angularMetric_vanish_Lb_right
  {n : ℕ}
  {nf : NullFrameData n}
  {X : Fin (n + 1) → ℝ} :
-- imply
  angularMetric n nf X nf.Lb = 0 := by
-- proof
  rw [angularMetric_comm]; exact angularMetric_vanish_Lb nf X

end NullFrame

namespace NullFrame

/--
[angularMetric_on_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean)
-/
@[path]
lemma angularMetric_on_e
  {n : ℕ}
  {nf : NullFrameData n}
  {i j : Fin (n - 1)} :
-- imply
  angularMetric n nf (nf.e i) (nf.e j) = if i = j then 1 else 0 := by
-- proof
  simp only [angularMetric, nf.e_orthonormal]
  by_cases h : i = j
  · subst h
    simp [Finset.sum_ite_eq']
  · simp only [h, ite_false]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = i <;> by_cases hkj : k = j
    · subst hki; subst hkj; exact absurd rfl h
    · subst hki; simp [h]
    · simp [hki]
    · simp [hki]

end NullFrame

namespace NullFrame

/--
[angularMetric_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean)
-/
@[path]
lemma angularMetric_nonneg
  {n : ℕ}
  {nf : NullFrameData n}
  {X : Fin (n + 1) → ℝ} :
-- imply
  0 ≤ angularMetric n nf X X := by
-- proof
  simp only [angularMetric]
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg _

end NullFrame

namespace NullFrame

/--
[angularMetric_pos_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean)
-/
@[path]
lemma angularMetric_pos_def
  {n : ℕ}
  {nf : NullFrameData n}
  {X : Fin (n + 1) → ℝ}
-- given
  (hL : minkowskiInner n nf.L X = 0)
  (hLb : minkowskiInner n nf.Lb X = 0)
  (hX : X ≠ 0) :
-- imply
  0 < angularMetric n nf X X := by
-- proof
  simp only [angularMetric]
  apply Finset.sum_pos'
  · intro i _; exact mul_self_nonneg _
  · by_contra h_none
    push Not at h_none
    apply hX
    have h_zero : ∀ i : Fin (n - 1), minkowskiInner n (nf.e i) X = 0 := by
      intro i
      have h1 := h_none i (Finset.mem_univ i)
      have h2 := mul_self_nonneg (minkowskiInner n (nf.e i) X)
      exact mul_self_eq_zero.mp (le_antisymm h1 h2)
    have := nf.completeness X
    rw [hLb, hL] at this
    simp only [mul_zero, zero_smul, zero_add] at this
    rw [this]
    simp only [h_zero, zero_smul, Finset.sum_const_zero]

end NullFrame

namespace NullFrame

/--
[minkowskiMetric_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean)
-/
@[path]
lemma minkowskiMetric_sq
  {n : ℕ} :
-- imply
  minkowskiMetric n * minkowskiMetric n = 1 := by
-- proof
  ext i j
  simp only [minkowskiMetric, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hij : i = j
  · subst hij; by_cases hi : (i : ℕ) = 0 <;> simp [hi]
  · by_cases hj : (j : ℕ) = 0 <;> simp [hij, hj]

end NullFrame

namespace NullFrame

/--
[minkowskiMetric_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean)
-/
@[path]
lemma minkowskiMetric_inv
  {n : ℕ} :
-- imply
  (minkowskiMetric n)⁻¹ = minkowskiMetric n :=
-- proof
  inv_eq_left_inv (minkowskiMetric_sq n)

end NullFrame

namespace NullFrame

/--
[minkowskiInner_eta_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean)
-/
@[path]
lemma minkowskiInner_eta_cancel
  {n : ℕ}
  {V W : Fin (n + 1) → ℝ} :
-- imply
  minkowskiInner n V (minkowskiMetric n *ᵥ W) = dotProduct V W := by
-- proof
  simp only [minkowskiInner, mulVec_mulVec, minkowskiMetric_sq, one_mulVec]

end NullFrame

namespace NullFrame

/--
[nullFrame_inverse_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean)
-/
@[path]
lemma nullFrame_inverse_decomposition
  {n : ℕ}
  {nf : NullFrameData n}
  {μ ν : Fin (n + 1)} :
-- imply
  (minkowskiMetric n)⁻¹ μ ν = -(1 / 2) * nf.L μ * nf.Lb ν - (1 / 2) * nf.Lb μ * nf.L ν + ∑ i : Fin (n - 1), nf.e i μ * nf.e i ν := by
-- proof
  rw [minkowskiMetric_inv]
  have h_entry : minkowskiMetric n μ ν = (minkowskiMetric n *ᵥ Pi.single ν 1) μ := by
    simp [mulVec, dotProduct, minkowskiMetric, Matrix.of_apply, Pi.single_apply]
  rw [h_entry]
  have h_comp := nf.completeness (minkowskiMetric n *ᵥ Pi.single ν 1)
  have h_μ := congr_fun h_comp μ
  rw [h_μ]
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    minkowskiInner_eta_cancel,
    dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  · ring
  · congr 1; ext i; ring

end NullFrame

namespace NullFrame

/--
[nullFrame_decomposition_full](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean)
-/
@[path]
lemma nullFrame_decomposition_full
  {n : ℕ}
  {nf : NullFrameData n} :
-- imply
  (∀ X Y : Fin (n + 1) → ℝ, minkowskiInner n X Y = -(1 / 2) * minkowskiInner n nf.L X * minkowskiInner n nf.Lb Y - (1 / 2) * minkowskiInner n nf.Lb X * minkowskiInner n nf.L Y + angularMetric n nf X Y) ∧ (∀ (X : Fin (n + 1) → ℝ), minkowskiInner n nf.L X = 0 → minkowskiInner n nf.Lb X = 0 → X ≠ 0 → 0 < angularMetric n nf X X) ∧ (∀ Y : Fin (n + 1) → ℝ, angularMetric n nf nf.L Y = 0) ∧ (∀ Y : Fin (n + 1) → ℝ, angularMetric n nf nf.Lb Y = 0) ∧ (∀ μ ν : Fin (n + 1), (minkowskiMetric n)⁻¹ μ ν = -(1 / 2) * nf.L μ * nf.Lb ν - (1 / 2) * nf.Lb μ * nf.L ν + ∑ i : Fin (n - 1), nf.e i μ * nf.e i ν) :=
-- proof
  ⟨nullFrame_decomposition nf,
    angularMetric_pos_def nf,
    angularMetric_vanish_L nf,
    angularMetric_vanish_Lb nf,
    nullFrame_inverse_decomposition nf⟩

end NullFrame


-- created on 2026-10-23
