import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.DistributionalKernels2
open DistributionalKernels
open scoped BigOperators SchwartzMap LineDeriv


namespace DistributionalKernels

/--
[multiIndexDistribDeriv_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionalKernels2.lean)
-/
@[path]
lemma multiIndexDistribDeriv_zero
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {v : 𝓢'(EuclideanSpace ℝ (Fin n), F)} :
-- imply
  multiIndexDistribDeriv 0 v = v := by
-- proof
  simp [multiIndexDistribDeriv, iterCoordDeriv]

end DistributionalKernels

namespace DistributionalKernels

/--
[distribMulPoly_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionalKernels2.lean)
-/
@[path]
lemma distribMulPoly_one
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {v : 𝓢'(EuclideanSpace ℝ (Fin n), F)} :
-- imply
  distribMulPoly (1 : MvPolynomial (Fin n) ℝ) v = v := by
-- proof
  unfold distribMulPoly
  ext φ
  simp only [TemperedDistributions.distribMulCLM_apply]
  congr 1; ext x
  simp [map_one, one_smul]

end DistributionalKernels

namespace DistributionalKernels

/--
[multiIndexLeqFinset_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionalKernels2.lean)
-/
@[path]
lemma multiIndexLeqFinset_zero
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F] :
-- imply
  multiIndexLeqFinset (0 : Fin n → ℕ) = {0} := by
-- proof
  ext α
  simp only [multiIndexLeqFinset, Fintype.mem_piFinset, Finset.mem_range,
    Finset.mem_singleton]
  constructor
  · intro h; ext i; have := h i; simp at this; omega
  · intro h; subst h; intro i; simp

end DistributionalKernels

namespace DistributionalKernels

/--
[iterCoordDeriv_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionalKernels2.lean)
-/
@[path]
lemma iterCoordDeriv_zero
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {j : Fin n}
  {v : 𝓢'(EuclideanSpace ℝ (Fin n), F)} :
-- imply
  iterCoordDeriv j 0 v = v := by
-- proof
  simp [iterCoordDeriv]

end DistributionalKernels

namespace DistributionalKernels

/--
[iterCoordDeriv_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionalKernels2.lean)
-/
@[path]
lemma iterCoordDeriv_succ
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {j : Fin n}
  {m : ℕ}
  {v : 𝓢'(EuclideanSpace ℝ (Fin n), F)} :
-- imply
  iterCoordDeriv j (m + 1) v = iterCoordDeriv j 1 (iterCoordDeriv j m v) := by
-- proof
  simp only [iterCoordDeriv, Function.iterate_succ_apply',
    Function.iterate_zero, Function.id_def]

end DistributionalKernels

namespace DistributionalKernels

/--
[multiIndexSize_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionalKernels2.lean)
-/
@[path]
lemma multiIndexSize_zero
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F] :
-- imply
  multiIndexSize (0 : Fin n → ℕ) = 0 := by
-- proof
  simp [multiIndexSize]

end DistributionalKernels

namespace DistributionalKernels

/--
[weightedDerivRHS_zero_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionalKernels2.lean)
-/
@[path]
lemma weightedDerivRHS_zero_eq
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {k : ℤ}
  {p : MvPolynomial (Fin n) ℝ}
  {coeffs : (Fin n → ℕ) → MvPolynomial (Fin n) ℝ}
  {v : 𝓢'(EuclideanSpace ℝ (Fin n), F)}
-- given
  (hc : coeffs 0 = p) :
-- imply
  weightedDerivRHS (0 : Fin n → ℕ) k coeffs v = distribMulPoly p (distribMulBracketPow k v) := by
-- proof
  unfold weightedDerivRHS
  rw [multiIndexLeqFinset_zero]
  simp only [Finset.sum_singleton]
  have h0 : (0 : Fin n → ℕ) - (0 : Fin n → ℕ) = 0 := by ext i; simp
  rw [h0, multiIndexDistribDeriv_zero, hc]
  congr 1
  have : multiIndexSize (0 : Fin n → ℕ) = 0 := multiIndexSize_zero
  simp [this]

end DistributionalKernels

namespace DistributionalKernels

/--
[distribDeriv_comm_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionalKernels2.lean)
-/
@[path]
lemma distribDeriv_comm_general
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {v w : EuclideanSpace ℝ (Fin n)}
  {T : 𝓢'(EuclideanSpace ℝ (Fin n), F)} :
-- imply
  TemperedDistributions.distribDerivCLM v (TemperedDistributions.distribDerivCLM w T) = TemperedDistributions.distribDerivCLM w (TemperedDistributions.distribDerivCLM v T) := by
-- proof
  ext φ
  simp only [TemperedDistributions.distribDerivCLM_apply, map_neg, neg_neg]
  congr 1
  exact (SchwartzRepresentation.schwartz_lineDerivOp_comm v w φ).symm

end DistributionalKernels

namespace DistributionalKernels

/--
[iterCoordDeriv_one_comm_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionalKernels2.lean)
-/
@[path]
lemma iterCoordDeriv_one_comm_one
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {j₀ j : Fin n}
  {v : 𝓢'(EuclideanSpace ℝ (Fin n), F)} :
-- imply
  iterCoordDeriv j₀ 1 (iterCoordDeriv j 1 v) = iterCoordDeriv j 1 (iterCoordDeriv j₀ 1 v) := by
-- proof
  simp only [iterCoordDeriv, Function.iterate_one]
  exact distribDeriv_comm_general _ _ _

end DistributionalKernels

namespace DistributionalKernels

/--
[iterCoordDeriv_one_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionalKernels2.lean)
-/
@[path]
lemma iterCoordDeriv_one_comm
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {j₀ j : Fin n}
  {m : ℕ}
  {v : 𝓢'(EuclideanSpace ℝ (Fin n), F)} :
-- imply
  iterCoordDeriv j₀ 1 (iterCoordDeriv j m v) = iterCoordDeriv j m (iterCoordDeriv j₀ 1 v) := by
-- proof
  induction m generalizing v with
  | zero => simp [iterCoordDeriv_zero]
  | succ m ih =>
    rw [iterCoordDeriv_succ j m v, iterCoordDeriv_succ j m (iterCoordDeriv j₀ 1 v)]
    rw [iterCoordDeriv_one_comm_one j₀ j (iterCoordDeriv j m v)]
    congr 1
    exact ih v

end DistributionalKernels

namespace DistributionalKernels

/--
[iterCoordDeriv_one_comm_foldl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionalKernels2.lean)
-/
@[path]
lemma iterCoordDeriv_one_comm_foldl
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {j₀ : Fin n}
  {γ : Fin n → ℕ}
  {l : List (Fin n)}
  {v : 𝓢'(EuclideanSpace ℝ (Fin n), F)} :
-- imply
  iterCoordDeriv j₀ 1 (l.foldl (fun w j => iterCoordDeriv j (γ j) w) v) = l.foldl (fun w j => iterCoordDeriv j (γ j) w) (iterCoordDeriv j₀ 1 v) := by
-- proof
  induction l generalizing v with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih (iterCoordDeriv i (γ i) v)]
    congr 1
    exact iterCoordDeriv_one_comm j₀ i (γ i) v

end DistributionalKernels

namespace DistributionalKernels

/--
[multiIndexDistribDeriv_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionalKernels2.lean)
-/
@[path]
lemma multiIndexDistribDeriv_step
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {n : ℕ}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {γ : Fin n → ℕ}
  {j₀ : Fin n}
  {v : 𝓢'(EuclideanSpace ℝ (Fin n), F)}
-- given
  (hj₀ : 0 < γ j₀) :
-- imply
  multiIndexDistribDeriv γ v = iterCoordDeriv j₀ 1 (multiIndexDistribDeriv (Function.update γ j₀ (γ j₀ - 1)) v) := by
-- proof
  unfold multiIndexDistribDeriv
  suffices h : ∀ (l : List (Fin n)) (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)),
    l.Nodup →
    l.foldl (fun w j => iterCoordDeriv j (γ j) w) v =
    if j₀ ∈ l then
      iterCoordDeriv j₀ 1
        (l.foldl (fun w j => iterCoordDeriv j (Function.update γ j₀ (γ j₀ - 1) j) w) v)
    else
      l.foldl (fun w j => iterCoordDeriv j (Function.update γ j₀ (γ j₀ - 1) j) w) v by
    have hmem : j₀ ∈ List.finRange n := List.mem_finRange j₀
    rw [h (List.finRange n) v (List.nodup_finRange n)]
    simp only [hmem, if_true]
  intro l
  induction l with
  | nil => intro v _; simp
  | cons i l ih =>
    intro v hnd
    simp only [List.foldl_cons]
    obtain ⟨hni, hndl⟩ := List.nodup_cons.mp hnd
    by_cases hij : i = j₀
    · subst hij
      simp only [List.mem_cons_self, if_true, Function.update_self]
      have hγ_eq : γ i = (γ i - 1) + 1 := by omega
      rw [hγ_eq, iterCoordDeriv_succ]
      rw [ih (iterCoordDeriv i 1 (iterCoordDeriv i (γ i - 1) v)) hndl]
      simp only [hni, if_false]
      rw [iterCoordDeriv_one_comm_foldl]
      have : γ i - 1 + 1 - 1 = γ i - 1 := by omega
      simp only [this]
    · have hne : i ≠ j₀ := hij
      rw [Function.update_of_ne hne]
      rw [ih (iterCoordDeriv i (γ i) v) hndl]
      by_cases hmem : j₀ ∈ l
      · simp only [List.mem_cons_of_mem i hmem, if_true, hmem, if_true]
      · simp only [show ¬ (j₀ ∈ i :: l) from fun h => by
        obtain h | h := List.mem_cons.mp h
        · exact hne h.symm
        · exact hmem h, if_false, hmem, if_false]
/-- Schwartz product rule for `p · ⟨x⟩^k · ∂_{j₀} u`: derivative is split between the polynomial-bracket factor and `u`. -/
end DistributionalKernels



-- created on 2026-10-23
