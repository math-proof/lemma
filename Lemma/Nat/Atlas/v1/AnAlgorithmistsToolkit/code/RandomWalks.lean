import Mathlib
import sympy.Basic
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.RandomWalks.Part2
open RandomWalks
open Matrix SimpleGraph Module.End Finset
open Finset Real BigOperators


namespace RandomWalks

/--
[stationaryDist_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
lemma stationaryDist_sum_eq_one
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hpos : (0 : ℝ) < ∑ u : V, (G.degree u : ℝ)) :
-- imply
  ∑ v : V, stationaryDist G v = 1 := by
-- proof
  simp only [stationaryDist]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hpos)

end RandomWalks

namespace RandomWalks

/--
[adjMatrix_row_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
lemma adjMatrix_row_sum
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : V} :
-- imply
  ∑ i : V, G.adjMatrix ℝ k i = (G.degree k : ℝ) := by
-- proof
  rw [G.degree_eq_sum_if_adj k]
  simp only [adjMatrix_apply]

end RandomWalks

namespace RandomWalks

/--
[degree_pos_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
lemma degree_pos_of_adj
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k x : V}
-- given
  (h : G.Adj k x) :
-- imply
  0 < G.degree x :=
-- proof
  Finset.card_pos.mpr ⟨k, by rwa [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]⟩

end RandomWalks

namespace RandomWalks

/--
[walkMatrix_stationaryVec_term](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
lemma walkMatrix_stationaryVec_term
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k x : V}
  {S : ℝ} :
-- imply
  G.adjMatrix ℝ k x / (G.degree x : ℝ) * ((G.degree x : ℝ) / S) = G.adjMatrix ℝ k x / S := by
-- proof
  simp only [adjMatrix_apply]
  split_ifs with h
  · have hd : (G.degree x : ℝ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp (degree_pos_of_adj G h)
    rw [one_div]
    field_simp
  · simp

end RandomWalks

namespace RandomWalks

/--
[walkMatrix_mulVec_stationaryVec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
lemma walkMatrix_mulVec_stationaryVec
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  (walkMatrix G).mulVec (stationaryVec G) = stationaryVec G := by
-- proof
  ext k
  simp only [mulVec, dotProduct, walkMatrix, stationaryVec]
  simp_rw [walkMatrix_stationaryVec_term G k _ _]
  rw [← Finset.sum_div, adjMatrix_row_sum]
section RegularGraph
variable {V : Type*} [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
end RegularGraph
section ConjugationEigenvalues

end RandomWalks

namespace RandomWalks

/--
[eigenspace_conj_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
lemma eigenspace_conj_eq
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  {e : M ≃ₗ[R] M}
  {f : Module.End R M}
  {μ : R} :
-- imply
  eigenspace (e.conj f) μ = Submodule.map (e : M →ₗ[R] M) (eigenspace f μ) := by
-- proof
  ext x
  simp only [Module.End.mem_eigenspace_iff, Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · intro h
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply e.injective
    simp only [LinearEquiv.conj_apply_apply] at h
    rwa [map_smul, e.apply_symm_apply]
  · rintro ⟨y, hy, rfl⟩
    show (e.conj f) (e y) = μ • (e y)
    rw [LinearEquiv.conj_apply_apply, e.symm_apply_apply, hy, map_smul]

end RandomWalks

namespace RandomWalks

/--
[hasEigenvalue_conj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
lemma hasEigenvalue_conj_iff
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  {e : M ≃ₗ[R] M}
  {f : Module.End R M}
  {μ : R} :
-- imply
  HasEigenvalue (e.conj f) μ ↔ HasEigenvalue f μ := by
-- proof
  simp only [hasEigenvalue_iff, eigenspace_conj_eq]
  constructor
  · intro h heq
    rw [heq, Submodule.map_bot] at h
    exact h rfl
  · intro h
    rw [Submodule.ne_bot_iff] at h ⊢
    obtain ⟨x, hx, hx_ne⟩ := h
    exact ⟨e x, Submodule.mem_map.mpr ⟨x, hx, rfl⟩,
      fun he => hx_ne (e.injective (by simpa using he))⟩
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

end RandomWalks

namespace RandomWalks

/--
[normWalkMatrix_eq_conj_rwMatrixGen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
lemma normWalkMatrix_eq_conj_rwMatrixGen
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [Fintype V]
  [DecidableEq V] :
-- imply
  normWalkMatrix G = Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) * rwMatrixGen G * Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ)) := by
-- proof
  simp only [normWalkMatrix, rwMatrixGen]
  suffices h : Matrix.diagonal (fun v => (G.degree v : ℝ)⁻¹) *
    Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ)) =
    Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) by
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    congr 1
    rw [Matrix.mul_assoc, h]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext v
  dsimp
  by_cases hd : (G.degree v : ℝ) = 0
  · simp [hd]
  · have hd_pos : (0 : ℝ) < (G.degree v : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by exact_mod_cast hd)
    have hsqrt_ne : Real.sqrt (G.degree v : ℝ) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr hd_pos
    have hsqrt_sq : Real.sqrt (G.degree v : ℝ) * Real.sqrt (G.degree v : ℝ) = (G.degree v : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hd_pos)
    field_simp
    rw [sq, hsqrt_sq]
section NormLapGen
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
end NormLapGen
section LazyWalk
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

end RandomWalks

namespace RandomWalks

/--
[adjMatrix_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
lemma adjMatrix_isHermitian
  [DecidableEq V] :
-- imply
  (G.adjMatrix ℝ).IsHermitian := by
-- proof
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, SimpleGraph.adjMatrix_apply,
    SimpleGraph.adj_comm]

end RandomWalks

namespace RandomWalks

/--
[normLazyWalkMatrix_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
lemma normLazyWalkMatrix_isHermitian
  [DecidableEq V]
  [Fintype V] :
-- imply
  (normLazyWalkMatrix G).IsHermitian := by
-- proof
  unfold normLazyWalkMatrix Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
  simp only [star_trivial]
  congr 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.diagonal_conjTranspose, star_trivial, (adjMatrix_isHermitian G).eq]
  rw [mul_assoc]

end RandomWalks

namespace RandomWalks

/--
[rwMatrixGen_eq_sqrt_mul_normWalkMatrix_mul_sqrt_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
lemma rwMatrixGen_eq_sqrt_mul_normWalkMatrix_mul_sqrt_inv
  [Fintype V]
  [DecidableEq V]
-- given
  (hpos : ∀ v : V, 0 < G.degree v) :
-- imply
  rwMatrixGen G = Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ)) * normWalkMatrix G * Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) := by
-- proof
  have hN := normWalkMatrix_eq_conj_rwMatrixGen G
  have hleft : Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ)) *
    (Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) *
    rwMatrixGen G *
    Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ))) *
    Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) =
    rwMatrixGen G := by
    simp only [Matrix.mul_assoc]
    rw [sqrtDeg_mul_sqrtDeg_inv G hpos, Matrix.mul_one]
    rw [← Matrix.mul_assoc, sqrtDeg_mul_sqrtDeg_inv G hpos, Matrix.one_mul]
  rw [← hleft, ← hN]

end RandomWalks

namespace RandomWalks

/--
[rwMatrixGen_eq_conj_normWalkMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
lemma rwMatrixGen_eq_conj_normWalkMatrix
  [Fintype V]
  [DecidableEq V]
-- given
  (hpos : ∀ v : V, 0 < G.degree v) :
-- imply
  Matrix.toLin' (rwMatrixGen G) = (sqrtDegEquiv G hpos).conj (Matrix.toLin' (normWalkMatrix G)) := by
-- proof
  have hW := rwMatrixGen_eq_sqrt_mul_normWalkMatrix_mul_sqrt_inv G hpos
  rw [hW]
  apply LinearMap.ext
  intro x
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [Matrix.toLin'_mul_apply, Matrix.toLin'_mul_apply]
  rfl

end RandomWalks

namespace RandomWalks

/--
[normWalkMatrix_rwMatrixGen_same_eigenvalues](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
lemma normWalkMatrix_rwMatrixGen_same_eigenvalues
  [Fintype V]
  [DecidableEq V]
  {μ : ℝ}
-- given
  (hpos : ∀ v : V, 0 < G.degree v) :
-- imply
  HasEigenvalue (Matrix.toLin' (normWalkMatrix G)) μ ↔ HasEigenvalue (Matrix.toLin' (rwMatrixGen G)) μ := by
-- proof
  rw [rwMatrixGen_eq_conj_normWalkMatrix G hpos]
  exact (hasEigenvalue_conj_iff (sqrtDegEquiv G hpos)
    (Matrix.toLin' (normWalkMatrix G)) μ).symm

end RandomWalks

namespace RandomWalks

/--
[hasEigenvalue_conj_graph_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
lemma hasEigenvalue_conj_graph_iff
  [Fintype V]
  [DecidableEq V]
  {μ : ℝ}
-- given
  (hpos : ∀ v : V, 0 < G.degree v) :
-- imply
  HasEigenvalue (Matrix.toLin' (rwMatrixGen G)) μ ↔ HasEigenvalue (Matrix.toLin' (normWalkMatrix G)) μ :=
-- proof
  (normWalkMatrix_rwMatrixGen_same_eigenvalues G hpos μ).symm

end RandomWalks

namespace RandomWalks

/--
[expander_matching_contraction_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
lemma expander_matching_contraction_ratio
  [Fintype L]
  [Fintype R]
  [DecidableEq L]
  [DecidableEq R]
  {G : SimpleGraph (L ⊕ R)}
  [DecidableRel G.Adj]
  {d : ℕ}
  {α β : ℝ}
  {Si : Finset L}
  {Si1_card : ℝ}
-- given
  (hbip : G.IsBipartiteOn)
  (hreg : G.IsRegularOfDegree d)
  (hexp : G.IsBipartiteExpander α β)
  (hd : (0 : ℝ) < (d : ℝ))
  (hSi : (Si.card : ℝ) ≤ α * (Fintype.card L : ℝ))
  (hSi_pos : (0 : ℝ) < (Si.card : ℝ))
  (hSi1 : Si1_card ≤ (Si.card : ℝ) - ((G.uniqueNeighbors Si).card : ℝ) / (d : ℝ)) :
-- imply
  Si1_card / (Si.card : ℝ) ≤ 2 * (1 - β / (d : ℝ)) := by
-- proof
  have hlem5 := G.unique_neighbors_lower_bound hbip hreg hexp Si hSi
  have h1 : (2 * β - ↑d) * (Si.card : ℝ) / (d : ℝ) ≤
    ((G.uniqueNeighbors Si).card : ℝ) / (d : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hd)
  have halg : (Si.card : ℝ) - (2 * β - ↑d) * (Si.card : ℝ) / (d : ℝ) =
    2 * (1 - β / (d : ℝ)) * (Si.card : ℝ) := by field_simp; ring
  have hcore : (Si.card : ℝ) - ((G.uniqueNeighbors Si).card : ℝ) / (d : ℝ) ≤
    2 * (1 - β / (d : ℝ)) * (Si.card : ℝ) := by linarith
  rw [div_le_iff₀ hSi_pos]
  linarith
end RandomWalks
namespace SimpleGraph
open Finset Real BigOperators
end SimpleGraph


/--
[sqrtDeg_mul_sqrtDeg_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
private lemma sqrtDeg_mul_sqrtDeg_inv_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (hpos : ∀ v : V, 0 < G.degree v) :
-- imply
  Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ)) * Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) = 1 := by
-- proof
  apply RandomWalks.sqrtDeg_mul_sqrtDeg_inv hpos

/--
[sqrtDeg_inv_mul_sqrtDeg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean)
-/
@[path]
private lemma sqrtDeg_inv_mul_sqrtDeg_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (hpos : ∀ v : V, 0 < G.degree v) :
-- imply
  Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) * Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ)) = 1 := by
-- proof
  apply RandomWalks.sqrtDeg_inv_mul_sqrtDeg hpos


-- created on 2026-10-23
