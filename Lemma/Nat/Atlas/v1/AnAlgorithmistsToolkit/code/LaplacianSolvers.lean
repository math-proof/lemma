import Mathlib
import sympy.Basic
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.LaplacianSolvers
open Matrix Finset BigOperators SimpleGraph Real An_Algorithmists_Toolkit
open SimpleGraph Finset
open scoped MatrixOrder ComplexOrder
open Matrix SimpleGraph Real


namespace An_Algorithmists_Toolkit

/--
[fin_telescope_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianSolvers.lean)
-/
@[path]
lemma fin_telescope_sum
  {k : ℕ}
  {f : Fin (k + 1) → ℝ} :
-- imply
  ∑ i : Fin k, (f (Fin.castSucc i) - f (Fin.succ i)) = f 0 - f (Fin.last k) := by
-- proof
  set g : ℕ → ℝ := fun i => if h : i < k + 1 then f ⟨i, h⟩ else 0
  have hg_eq : ∀ i : Fin k,
    f (Fin.castSucc i) - f (Fin.succ i) = g i.val - g (i.val + 1) := by
    intro ⟨i, hi⟩
    simp only [g, Fin.castSucc_mk, Fin.succ_mk,
      show i < k + 1 from Nat.lt_succ_of_lt hi,
      show i + 1 < k + 1 from Nat.succ_lt_succ hi, dite_true]
  have hsum_eq : ∑ i : Fin k, (f (Fin.castSucc i) - f (Fin.succ i)) =
    ∑ i : Fin k, (g i.val - g (i.val + 1)) :=
    Finset.sum_congr rfl (fun i _ => hg_eq i)
  rw [hsum_eq, Fin.sum_univ_eq_sum_range (fun i => g i - g (i + 1))]
  rw [Finset.sum_range_sub' g k]
  simp only [g, show (0 : ℕ) < k + 1 from Nat.zero_lt_succ k,
    show k < k + 1 from Nat.lt_succ_iff.mpr le_rfl, dite_true]
  rfl

end An_Algorithmists_Toolkit

namespace An_Algorithmists_Toolkit

/--
[edge_loewner_path](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianSolvers.lean)
-/
@[path]
lemma edge_loewner_path
  {n : ℕ}
  {k : ℕ}
  {path : Fin (k + 1) → Fin n}
  {u v : Fin n}
  {L_e : Matrix (Fin n) (Fin n) ℝ}
  {L_path : Matrix (Fin n) (Fin n) ℝ}
  {x : Fin n → ℝ}
-- given
  (hk : 0 < k)
  (hinj : Function.Injective path)
  (hu : path 0 = u)
  (hv : path ⟨k, Nat.lt_succ_iff.mpr le_rfl⟩ = v)
  (hLe : ∀ x : Fin n → ℝ, dotProduct x (L_e.mulVec x) = (x u - x v) ^ 2)
  (hLp : ∀ x : Fin n → ℝ, dotProduct x (L_path.mulVec x) = ∑ i : Fin k, (x (path (Fin.castSucc i)) - x (path (Fin.succ i))) ^ 2) :
-- imply
  dotProduct x (L_e.mulVec x) ≤ k * dotProduct x (L_path.mulVec x) := by
-- proof
  rw [hLe, hLp]
  have htele : x u - x v =
    ∑ i : Fin k, (x (path (Fin.castSucc i)) - x (path (Fin.succ i))) := by
    have h := fin_telescope_sum k (x ∘ path)
    simp only [Function.comp] at h
    have h0 : x (path 0) = x u := by rw [hu]
    have hk' : x (path (Fin.last k)) = x v := by
      congr 1
    linarith
  calc (x u - x v) ^ 2
    = (∑ i : Fin k, (x (path (Fin.castSucc i)) - x (path (Fin.succ i)))) ^ 2 := by
      rw [htele]
    _ ≤ ↑k * ∑ i : Fin k, (x (path (Fin.castSucc i)) - x (path (Fin.succ i))) ^ 2 := by
      have cs := @sq_sum_le_card_mul_sum_sq (Fin k) ℝ _ _ _ _
        Finset.univ (fun i => x (path (Fin.castSucc i)) - x (path (Fin.succ i)))
      simpa [Finset.card_univ, Fintype.card_fin] using cs

end An_Algorithmists_Toolkit

namespace An_Algorithmists_Toolkit

/--
[steepest_descent_eigenvector_convergence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianSolvers.lean)
-/
@[path]
lemma steepest_descent_eigenvector_convergence
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
  {e_i : Fin n → ℝ}
  {μ : ℝ}
  {e_next : Fin n → ℝ}
-- given
  (he_nz : e_i ≠ 0)
  (hμ : μ ≠ 0)
  (heig : A.mulVec e_i = μ • e_i)
  (he_next : e_next = e_i - (dotProduct (A.mulVec e_i) (A.mulVec e_i) / dotProduct (A.mulVec e_i) (A.mulVec (A.mulVec e_i))) • A.mulVec e_i) :
-- imply
  e_next = 0 := by
-- proof
  subst he_next
  rw [heig, mulVec_smul, heig]
  simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
  have hdot_ne : dotProduct e_i e_i ≠ 0 := by
    intro h; exact he_nz (dotProduct_self_eq_zero.mp h)
  have hfrac : μ * (μ * (e_i ⬝ᵥ e_i)) / (μ * (μ * (μ * (e_i ⬝ᵥ e_i)))) = μ⁻¹ := by
    field_simp
  rw [hfrac]
  simp only [smul_smul, inv_mul_cancel₀ hμ, one_smul, sub_self]

end An_Algorithmists_Toolkit

namespace An_Algorithmists_Toolkit

/--
[iter_error_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianSolvers.lean)
-/
@[path]
lemma iter_error_step
  {n : ℕ}
  {A L S : Matrix (Fin n) (Fin n) ℝ}
  [Invertible L]
  {b : Fin n → ℝ}
  {x_star : Fin n → ℝ}
  {xk : Fin n → ℝ}
-- given
  (hA : A = L + S)
  (hx : A.mulVec x_star = b) :
-- imply
  (⅟L).mulVec (b - S.mulVec xk) - x_star = -((⅟L * S).mulVec (xk - x_star)) := by
-- proof
  have hb : b = (L + S).mulVec x_star := by rw [← hA, hx]
  rw [hb, add_mulVec, mulVec_sub, mulVec_sub, mulVec_add]
  simp only [mulVec_mulVec, invOf_mul_self, one_mulVec]
  ring

end An_Algorithmists_Toolkit

namespace An_Algorithmists_Toolkit

/--
[iterative_solver_convergence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianSolvers.lean)
-/
@[path]
lemma iterative_solver_convergence
  {n : ℕ}
  {A L S : Matrix (Fin n) (Fin n) ℝ}
  [Invertible L]
  {ρ : ℝ}
  {b : Fin n → ℝ}
  {x_star : Fin n → ℝ}
  {x : ℕ → Fin n → ℝ}
  {k : ℕ}
-- given
  (hA : A = L + S)
  (hρ : ρ < 1)
  (hρ_pos : 0 ≤ ρ)
  (hρ_spec : ∀ v : Fin n → ℝ, ‖(⅟L * S).mulVec v‖ ≤ ρ * ‖v‖)
  (hx : A.mulVec x_star = b)
  (hiter : ∀ k, x (k+1) = (⅟L).mulVec (b - S.mulVec (x k))) :
-- imply
  ‖x k - x_star‖ ≤ ρ ^ k * ‖x 0 - x_star‖ := by
-- proof
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : x (k + 1) - x_star = -((⅟L * S).mulVec (x k - x_star)) := by
      rw [hiter k]
      exact iter_error_step A L S hA b x_star hx (x k)
    rw [hstep, norm_neg]
    calc ‖(⅟L * S).mulVec (x k - x_star)‖
      ≤ ρ * ‖x k - x_star‖ := hρ_spec _
      _ ≤ ρ * (ρ ^ k * ‖x 0 - x_star‖) := by
        apply mul_le_mul_of_nonneg_left ih hρ_pos
      _ = ρ ^ (k + 1) * ‖x 0 - x_star‖ := by ring
end An_Algorithmists_Toolkit
open SimpleGraph Finset
namespace LowStretchSpanningTree



-- created on 2026-10-23
