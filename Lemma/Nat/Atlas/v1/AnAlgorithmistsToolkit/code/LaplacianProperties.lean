import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.AnAlgorithmistsToolkit.code.LaplacianProperties
open Matrix SimpleGraph Finset BigOperators PSDMatrix LaplacianProperties
open scoped MatrixOrder
open Matrix SimpleGraph Finset BigOperators Polynomial


namespace PSDMatrix

/--
[isPSD_iff_eigenvalues_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma isPSD_iff_eigenvalues_nonneg
  [Fintype n]
  [DecidableEq n]
  {M : Matrix n n ℝ}
-- given
  (hM : M.IsHermitian) :
-- imply
  IsPSD M ↔ ∀ i, 0 ≤ hM.eigenvalues i := by
-- proof
  rw [show IsPSD M ↔ M.PosSemidef from Iff.rfl, hM.posSemidef_iff_eigenvalues_nonneg, Pi.le_def]
  simp

end PSDMatrix

namespace PSDMatrix

/--
[isPD_iff_eigenvalues_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma isPD_iff_eigenvalues_pos
  [Fintype n]
  [DecidableEq n]
  {M : Matrix n n ℝ}
-- given
  (hM : M.IsHermitian) :
-- imply
  IsPD M ↔ ∀ i, 0 < hM.eigenvalues i :=
-- proof
  hM.posDef_iff_eigenvalues_pos

end PSDMatrix

namespace PSDMatrix

/--
[isPSD_and_isPD_iff_eigenvalues](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma isPSD_and_isPD_iff_eigenvalues
  [Fintype n]
  [DecidableEq n]
  {M : Matrix n n ℝ}
-- given
  (hM : M.IsHermitian) :
-- imply
  (IsPSD M ↔ ∀ i, 0 ≤ hM.eigenvalues i) ∧ (IsPD M ↔ ∀ i, 0 < hM.eigenvalues i) :=
-- proof
  ⟨isPSD_iff_eigenvalues_nonneg hM, isPD_iff_eigenvalues_pos hM⟩
open scoped MatrixOrder

end PSDMatrix

namespace PSDMatrix

/--
[star_eq_transpose](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma star_eq_transpose
  [Fintype n]
  [DecidableEq n]
  {B : Matrix n n ℝ} :
-- imply
  star B = Bᵀ := by
-- proof
  ext i j; simp [star, Matrix.transpose]

end PSDMatrix

namespace PSDMatrix

/--
[conjTranspose_eq_transpose_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma conjTranspose_eq_transpose_real
  [Fintype n]
  [Fintype m]
  {B : Matrix m n ℝ} :
-- imply
  B.conjTranspose = Bᵀ := by
-- proof
  ext i j; simp [conjTranspose]

end PSDMatrix

namespace PSDMatrix

/--
[isPSD_iff_exists_transpose_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma isPSD_iff_exists_transpose_mul_self
  [Fintype n]
  [DecidableEq n]
  {M : Matrix n n ℝ} :
-- imply
  IsPSD M ↔ ∃ B : Matrix n n ℝ, M = Bᵀ * B := by
-- proof
  constructor
  ·
    intro hM
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
    exact ⟨B, by rwa [star_eq_transpose] at hB⟩
  ·
    rintro ⟨B, rfl⟩
    rw [← conjTranspose_eq_transpose_real]
    exact posSemidef_conjTranspose_mul_self B
universe u_psd in

end PSDMatrix

namespace PSDMatrix

/--
[isPSD_iff_exists_transpose_mul_self_rect](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma isPSD_iff_exists_transpose_mul_self_rect
  {n : Type u_psd}
  [Fintype n]
  [DecidableEq n]
  {M : Matrix n n ℝ} :
-- imply
  IsPSD M ↔ ∃ (k : Type u_psd) (_ : Fintype k) (B : Matrix k n ℝ), M = Bᵀ * B := by
-- proof
  constructor
  ·
    intro hM
    obtain ⟨B, hB⟩ := (isPSD_iff_exists_transpose_mul_self M).mp hM
    exact ⟨n, inferInstance, B, hB⟩
  ·
    rintro ⟨k, fk, B, rfl⟩
    rw [← conjTranspose_eq_transpose_real]
    exact posSemidef_conjTranspose_mul_self B
end PSDMatrix
open Matrix SimpleGraph Finset BigOperators
namespace LaplacianProperties
open Matrix SimpleGraph Finset BigOperators


namespace LaplacianProperties

/--
[eq_of_adj_of_mulVec_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma eq_of_adj_of_mulVec_eq_zero
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V → ℝ}
  {i j : V}
-- given
  (hx : (G.lapMatrix ℝ).mulVec x = 0)
  (hadj : G.Adj i j) :
-- imply
  x i = x j := by
-- proof
  have hdot : x ⬝ᵥ ((G.lapMatrix ℝ).mulVec x) = 0 := by
    rw [hx]; simp [dotProduct]
  have hqf := lapMatrix_toLinearMap₂' ℝ G x
  rw [toLinearMap₂'_apply'] at hqf
  rw [hdot] at hqf
  have hsum_zero : (∑ a : V, ∑ b : V, if G.Adj a b then (x a - x b) ^ 2 else 0) = (0 : ℝ) := by
    linarith
  have hinner_nonneg : ∀ a ∈ Finset.univ,
    (0 : ℝ) ≤ ∑ b : V, if G.Adj a b then (x a - x b) ^ 2 else 0 := by
    intro a _; exact Finset.sum_nonneg (fun b _ => by split_ifs <;> positivity)
  have hi_zero :=
    ((Finset.sum_eq_zero_iff_of_nonneg hinner_nonneg).mp hsum_zero) i (mem_univ i)
  have hterm_nonneg : ∀ b ∈ Finset.univ,
    (0 : ℝ) ≤ if G.Adj i b then (x i - x b) ^ 2 else 0 := by
    intro b _; split_ifs <;> positivity
  have hj :=
    ((Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hi_zero) j (mem_univ j)
  simp only [hadj, ite_true] at hj
  nlinarith [sq_nonneg (x i - x j)]

end LaplacianProperties

namespace LaplacianProperties

/--
[eq_const_of_adj_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma eq_const_of_adj_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V → ℝ}
  {v₀ w : V}
-- given
  (hconn : G.Connected)
  (hadj_eq : ∀ i j : V, G.Adj i j → x i = x j) :
-- imply
  x w = x v₀ := by
-- proof
  have hreach := hconn.preconnected v₀ w
  rw [reachable_eq_reflTransGen] at hreach
  induction hreach with
  | refl => rfl
  | tail _ hadj ih => exact (hadj_eq _ _ hadj).symm ▸ ih

end LaplacianProperties

namespace LaplacianProperties

/--
[ker_lapMatrix_eq_span_ones](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma ker_lapMatrix_eq_span_ones
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hconn : G.Connected) :
-- imply
  LinearMap.ker (G.lapMatrix ℝ).mulVecLin = Submodule.span ℝ {fun _ : V => (1 : ℝ)} := by
-- proof
  ext x
  rw [LinearMap.mem_ker, mulVecLin_apply, Submodule.mem_span_singleton]
  constructor
  ·
    intro hx
    obtain ⟨v₀⟩ := hconn.nonempty
    have hadj_eq := eq_of_adj_of_mulVec_eq_zero G x hx
    have hconst := eq_const_of_adj_eq G hconn x hadj_eq v₀
    exact ⟨x v₀, by
      ext w
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      exact (hconst w).symm⟩
  ·
    rintro ⟨c, rfl⟩
    rw [mulVec_smul, lapMatrix_mulVec_const_eq_zero]
    exact smul_zero c
open Matrix SimpleGraph Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
section EdgeUnion
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
set_option linter.unusedSectionVars false in

end LaplacianProperties

namespace LaplacianProperties

/--
[adjMatrix_sup_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma adjMatrix_sup_of_disjoint
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G H : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
-- given
  (hd : Disjoint G H) :
-- imply
  (G ⊔ H).adjMatrix ℝ = G.adjMatrix ℝ + H.adjMatrix ℝ := by
-- proof
  classical
  ext i j
  simp only [SimpleGraph.adjMatrix_apply, Matrix.add_apply, sup_adj]
  have hne : ¬(G.Adj i j ∧ H.Adj i j) := by
    intro ⟨hG, hH⟩
    have hinf : G ⊓ H = ⊥ := disjoint_iff.mp hd
    have := (inf_adj G H i j).mpr ⟨hG, hH⟩
    rw [hinf] at this
    exact (bot_adj i j).mp this
  by_cases hG : G.Adj i j <;> by_cases hH : H.Adj i j <;> simp_all

end LaplacianProperties

namespace LaplacianProperties

/--
[degree_sup_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma degree_sup_of_disjoint
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G H : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {v : V}
-- given
  (hd : Disjoint G H) :
-- imply
  (G ⊔ H).degree v = G.degree v + H.degree v := by
-- proof
  classical
  have hinf : G ⊓ H = ⊥ := disjoint_iff.mp hd
  simp only [SimpleGraph.degree]
  have hdisjoint : Disjoint (G.neighborFinset v) (H.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [SimpleGraph.mem_neighborFinset] at hw1 hw2
    have := (inf_adj G H v w).mpr ⟨hw1, hw2⟩
    rw [hinf] at this
    exact (bot_adj v w).mp this
  have heq : (G ⊔ H).neighborFinset v = G.neighborFinset v ∪ H.neighborFinset v := by
    ext w
    simp [SimpleGraph.mem_neighborFinset, sup_adj]
  rw [heq]
  exact Finset.card_union_of_disjoint hdisjoint

end LaplacianProperties

namespace LaplacianProperties

/--
[degMatrix_sup_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma degMatrix_sup_of_disjoint
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G H : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
-- given
  (hd : Disjoint G H) :
-- imply
  (G ⊔ H).degMatrix ℝ = G.degMatrix ℝ + H.degMatrix ℝ := by
-- proof
  classical
  ext i j
  simp only [SimpleGraph.degMatrix, Matrix.diagonal_apply, Matrix.add_apply]
  split_ifs with h
  · subst h
    push_cast [degree_sup_of_disjoint G H hd i]
    ring
  · simp

end LaplacianProperties

namespace LaplacianProperties

/--
[lapMatrix_sup_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma lapMatrix_sup_of_disjoint
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G H : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
-- given
  (hd : Disjoint G H) :
-- imply
  (G ⊔ H).lapMatrix ℝ = G.lapMatrix ℝ + H.lapMatrix ℝ := by
-- proof
  classical
  simp only [SimpleGraph.lapMatrix]
  rw [degMatrix_sup_of_disjoint G H hd, adjMatrix_sup_of_disjoint G H hd]
  abel

end LaplacianProperties

namespace LaplacianProperties

/--
[not_adj_of_degree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma not_adj_of_degree_zero
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V}
  {j : V}
-- given
  (hdeg : G.degree v = 0) :
-- imply
  ¬G.Adj v j := by
-- proof
  intro hadj
  have hmem := (G.mem_neighborFinset v j).mpr hadj
  rw [SimpleGraph.degree, Finset.card_eq_zero] at hdeg
  simp [hdeg] at hmem

end LaplacianProperties

namespace LaplacianProperties

/--
[lapMatrix_row_eq_zero_of_degree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma lapMatrix_row_eq_zero_of_degree_zero
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V}
  {j : V}
-- given
  (hdeg : G.degree v = 0) :
-- imply
  G.lapMatrix ℝ v j = 0 := by
-- proof
  by_cases hvj : v = j
  · subst hvj
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.diagonal,
      SimpleGraph.adjMatrix_apply, hdeg]
  · have hnadj : ¬G.Adj v j := not_adj_of_degree_zero G hdeg j
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.diagonal, hvj,
      SimpleGraph.adjMatrix_apply, hnadj]

end LaplacianProperties

namespace LaplacianProperties

/--
[lapMatrix_col_eq_zero_of_degree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma lapMatrix_col_eq_zero_of_degree_zero
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V}
  {j : V}
-- given
  (hdeg : G.degree v = 0) :
-- imply
  G.lapMatrix ℝ j v = 0 := by
-- proof
  have hsymm : (G.lapMatrix ℝ).IsSymm := SimpleGraph.isSymm_lapMatrix ℝ G
  rw [hsymm.apply v j]
  exact lapMatrix_row_eq_zero_of_degree_zero G hdeg j

end LaplacianProperties

namespace LaplacianProperties

/--
[lapMatrix_eq_zero_of_degree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma lapMatrix_eq_zero_of_degree_zero
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V}
  {j : V}
-- given
  (hdeg : G.degree v = 0) :
-- imply
  G.lapMatrix ℝ v j = 0 ∧ G.lapMatrix ℝ j v = 0 :=
-- proof
  ⟨lapMatrix_row_eq_zero_of_degree_zero G hdeg j, lapMatrix_col_eq_zero_of_degree_zero G hdeg j⟩

end LaplacianProperties

namespace LaplacianProperties

/--
[dim_ker_lapMatrix_eq_card_connectedComponent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean)
-/
@[path]
lemma dim_ker_lapMatrix_eq_card_connectedComponent
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Module.finrank ℝ (LinearMap.ker (G.lapMatrix ℝ).mulVecLin) = Fintype.card G.ConnectedComponent := by
-- proof
  have h : (G.lapMatrix ℝ).mulVecLin = (G.lapMatrix ℝ).toLin' := by
    ext x; simp [Matrix.toLin'_apply']
  rwa [h]
open Matrix SimpleGraph Finset BigOperators Polynomial
open Matrix SimpleGraph Finset BigOperators
open Matrix SimpleGraph Finset BigOperators

end LaplacianProperties


-- created on 2026-10-23
