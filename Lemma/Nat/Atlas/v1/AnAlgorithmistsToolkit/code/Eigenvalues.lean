import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.Eigenvalues
open Module.End SimpleGraph Finset BigOperators Matrix
open Matrix SimpleGraph Finset BigOperators
open Matrix SimpleGraph Finset BigOperators Module.End


namespace EigenvalueBounds

/--
[trace_lapMatrix_eq_sum_degrees](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Eigenvalues.lean)
-/
@[path]
lemma trace_lapMatrix_eq_sum_degrees
  [Fintype V]
  [DecidableEq V]
  (G : SimpleGraph V)
  [DecidableRel G.Adj] :
-- imply
  (G.lapMatrix ℝ).trace = ∑ v : V, (G.degree v : ℝ) := by
-- proof
  unfold SimpleGraph.lapMatrix
  rw [Matrix.trace_sub, SimpleGraph.trace_adjMatrix, sub_zero]
  unfold SimpleGraph.degMatrix
  rw [Matrix.trace_diagonal]

end EigenvalueBounds

namespace EigenvalueBounds

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
/--
[sum_eigenvalues₀_eq_sum_degrees](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Eigenvalues.lean)
-/
@[path]
lemma sum_eigenvalues₀_eq_sum_degrees :
  let hL := isHermitian_lapMatrix ℝ G
  ∑ i, hL.eigenvalues₀ i = ∑ v : V, (G.degree v : ℝ) := by
  intro hL
  have hreindex : ∑ i, hL.eigenvalues₀ i = ∑ i, hL.eigenvalues i := by
    simp only [IsHermitian.eigenvalues]
    rw [← Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm]
  rw [hreindex]
  have h := hL.trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id] at h
  linarith [trace_lapMatrix_eq_sum_degrees G]

end EigenvalueBounds

namespace EigenvalueBounds

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
/--
[sum_eigenvalues₀_eq_sum_degrees_le_maxDegree_mul_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Eigenvalues.lean)
-/
@[path]
lemma sum_eigenvalues₀_eq_sum_degrees_le_maxDegree_mul_card :
  let hL := isHermitian_lapMatrix ℝ G
  (∑ i, hL.eigenvalues₀ i = ∑ v : V, (G.degree v : ℝ)) ∧
  (∑ v : V, (G.degree v : ℝ)) ≤ (G.maxDegree : ℝ) * (Fintype.card V : ℝ) := by
  refine ⟨sum_eigenvalues₀_eq_sum_degrees G, ?_⟩
  calc ∑ v : V, (G.degree v : ℝ)
    ≤ ∑ _v : V, (G.maxDegree : ℝ) := by
        apply Finset.sum_le_sum
        intro v _
        exact_mod_cast G.degree_le_maxDegree v
    _ = (G.maxDegree : ℝ) * (Fintype.card V : ℝ) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

end EigenvalueBounds

namespace EigenvalueBounds

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
/--
[eigenvalues₀_min_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Eigenvalues.lean)
-/
@[path]
lemma eigenvalues₀_min_eq_zero [Nonempty V] :
  let hL := isHermitian_lapMatrix ℝ G
  hL.eigenvalues₀ ⟨Fintype.card V - 1, Nat.sub_lt Fintype.card_pos Nat.one_pos⟩ = 0 := by
  intro hL
  have hPSD := posSemidef_lapMatrix ℝ G
  have hnn : ∀ i, 0 ≤ hL.eigenvalues i := hPSD.eigenvalues_nonneg
  have hexists : ∃ i, hL.eigenvalues i = 0 := by
    by_contra h; push Not at h
    have hpos : ∀ i, 0 < hL.eigenvalues i :=
      fun i => lt_of_le_of_ne (hnn i) (Ne.symm (h i))
    have hPD : (lapMatrix ℝ G).PosDef := hL.posDef_iff_eigenvalues_pos.mpr hpos
    rw [posDef_iff_dotProduct_mulVec] at hPD
    have h1 : (G.lapMatrix ℝ).mulVec (fun _ => (1 : ℝ)) = 0 := by
      ext v
      simp [SimpleGraph.lapMatrix_mulVec_apply']
    have hne : (fun (_ : V) => (1 : ℝ)) ≠ 0 := by
      intro heq; have := congr_fun heq (Classical.arbitrary V); simp at this
    have hgt := hPD.2 hne; simp only [star_trivial] at hgt; rw [h1] at hgt
    simp [dotProduct_zero] at hgt
  obtain ⟨i, hi⟩ := hexists
  have heq₀ : hL.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) = 0 := by
    simp only [IsHermitian.eigenvalues] at hi; exact hi
  let idx : Fin (Fintype.card V) :=
    ⟨Fintype.card V - 1, Nat.sub_lt Fintype.card_pos Nat.one_pos⟩
  have hlast_le : hL.eigenvalues₀ idx ≤ 0 := by
    calc hL.eigenvalues₀ idx
      ≤ hL.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) := by
          apply hL.eigenvalues₀_antitone; simp only [idx, Fin.le_def]; omega
      _ = 0 := heq₀
  have hlast_nn : 0 ≤ hL.eigenvalues₀ idx := by
    have : hL.eigenvalues₀ idx =
      hL.eigenvalues ((Fintype.equivOfCardEq (Fintype.card_fin _)) idx) := by
      simp [IsHermitian.eigenvalues]
    rw [this]; exact hnn _
  linarith

end EigenvalueBounds

namespace EigenvalueBounds

/--
[eigenvalue_second_smallest_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Eigenvalues.lean)
-/
@[path]
lemma eigenvalue_second_smallest_le
  [Fintype V]
  [DecidableEq V]
  (G : SimpleGraph V)
  [DecidableRel G.Adj]
-- given
  (hn : Fintype.card V ≥ 2) :
-- imply
  let hL := isHermitian_lapMatrix ℝ G
  let n := Fintype.card V
  hL.eigenvalues₀ ⟨n - 2, by omega⟩ ≤ (∑ v : V, (G.degree v : ℝ)) / ((n : ℝ) - 1) := by
-- proof
  intro hL n
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hsum := sum_eigenvalues₀_eq_sum_degrees G
  have hmin : hL.eigenvalues₀ ⟨n - 1, by omega⟩ = 0 := eigenvalues₀_min_eq_zero G
  have hrest : ∑ i ∈ univ.erase (⟨n - 1, by omega⟩ : Fin n),
    hL.eigenvalues₀ i = ∑ v : V, (G.degree v : ℝ) := by
    have := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
      hL.eigenvalues₀ (Finset.mem_univ ⟨n - 1, by omega⟩)
    linarith
  have hcard : (univ.erase (⟨n - 1, by omega⟩ : Fin n)).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hge : ∀ i ∈ univ.erase (⟨n - 1, by omega⟩ : Fin n),
    hL.eigenvalues₀ ⟨n - 2, by omega⟩ ≤ hL.eigenvalues₀ i := by
    intro i hi
    apply hL.eigenvalues₀_antitone; simp only [Fin.le_def]
    have hne : i ≠ ⟨n - 1, by omega⟩ := Finset.ne_of_mem_erase hi
    have : i.val ≠ n - 1 := fun heq => hne (Fin.ext heq)
    omega
  have hsum_ge := Finset.card_nsmul_le_sum _ _ _ hge
  rw [hcard] at hsum_ge; simp only [nsmul_eq_mul] at hsum_ge; rw [hrest] at hsum_ge
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := Nat.ofNat_le_cast.mpr hn; linarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
  rw [hcast] at hsum_ge
  rw [le_div_iff₀ hn1_pos]
  linarith [mul_comm (hL.eigenvalues₀ ⟨n - 2, by omega⟩) ((n : ℝ) - 1)]

end EigenvalueBounds

namespace EigenvalueBounds

/--
[eigenvalue_largest_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Eigenvalues.lean)
-/
@[path]
lemma eigenvalue_largest_ge
  [Fintype V]
  [DecidableEq V]
  (G : SimpleGraph V)
  [DecidableRel G.Adj]
-- given
  (hn : Fintype.card V ≥ 2) :
-- imply
  let hL := isHermitian_lapMatrix ℝ G
  let n := Fintype.card V
  hL.eigenvalues₀ ⟨0, by omega⟩ ≥ (∑ v : V, (G.degree v : ℝ)) / ((n : ℝ) - 1) := by
-- proof
  intro hL n
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hsum := sum_eigenvalues₀_eq_sum_degrees G
  have hmin : hL.eigenvalues₀ ⟨n - 1, by omega⟩ = 0 := eigenvalues₀_min_eq_zero G
  have hrest : ∑ i ∈ univ.erase (⟨n - 1, by omega⟩ : Fin n),
    hL.eigenvalues₀ i = ∑ v : V, (G.degree v : ℝ) := by
    have := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
      hL.eigenvalues₀ (Finset.mem_univ ⟨n - 1, by omega⟩)
    linarith
  have hcard : (univ.erase (⟨n - 1, by omega⟩ : Fin n)).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hle : ∀ i ∈ univ.erase (⟨n - 1, by omega⟩ : Fin n),
    hL.eigenvalues₀ i ≤ hL.eigenvalues₀ ⟨0, by omega⟩ := by
    intro i _
    apply hL.eigenvalues₀_antitone
    exact Fin.mk_le_mk.mpr (Nat.zero_le _)
  have hsum_le := Finset.sum_le_card_nsmul _ _ _ hle
  rw [hcard] at hsum_le; simp only [nsmul_eq_mul] at hsum_le; rw [hrest] at hsum_le
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := Nat.ofNat_le_cast.mpr hn; linarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
  rw [hcast] at hsum_le
  rw [ge_iff_le, div_le_iff₀ hn1_pos]
  linarith [mul_comm (hL.eigenvalues₀ ⟨0, by omega⟩) ((n : ℝ) - 1)]

end EigenvalueBounds

namespace EigenvalueBounds

/--
[lemma22_eigenvalue_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Eigenvalues.lean)
-/
@[path]
lemma lemma22_eigenvalue_bounds
  [Fintype V]
  [DecidableEq V]
  (G : SimpleGraph V)
  [DecidableRel G.Adj]
-- given
  (hn : Fintype.card V ≥ 2) :
-- imply
  let hL := isHermitian_lapMatrix ℝ G
  let n := Fintype.card V
  hL.eigenvalues₀ ⟨n - 2, by omega⟩ ≤ (∑ v : V, (G.degree v : ℝ)) / ((n : ℝ) - 1) ∧
    hL.eigenvalues₀ ⟨0, by omega⟩ ≥ (∑ v : V, (G.degree v : ℝ)) / ((n : ℝ) - 1) :=
-- proof
  ⟨eigenvalue_second_smallest_le G hn, eigenvalue_largest_ge G hn⟩
end EigenvalueBounds
open Module.End SimpleGraph Finset BigOperators
namespace Matrix
section LapMatrixNullSpace


namespace Matrix

/--
[eq_of_adj_of_lapMatrix_mulVec_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Eigenvalues.lean)
-/
@[path]
lemma eq_of_adj_of_lapMatrix_mulVec_eq_zero
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

end Matrix

namespace Matrix

/--
[eq_const_of_adj_eq_connected](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Eigenvalues.lean)
-/
@[path]
lemma eq_const_of_adj_eq_connected
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

end Matrix

namespace Matrix

/--
[lapMatrix_eigenspace_zero_eq_span_ones](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Eigenvalues.lean)
-/
@[path]
lemma lapMatrix_eigenspace_zero_eq_span_ones
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hconn : G.Connected) :
-- imply
  eigenspace (G.lapMatrix ℝ).mulVecLin 0 = Submodule.span ℝ {fun _ : V => (1 : ℝ)} := by
-- proof
  rw [eigenspace_zero]
  ext x
  rw [LinearMap.mem_ker, mulVecLin_apply, Submodule.mem_span_singleton]
  constructor
  · intro hx
    obtain ⟨v₀⟩ := hconn.nonempty
    have hadj_eq : ∀ i j, G.Adj i j → x i = x j :=
      fun i j hadj => eq_of_adj_of_lapMatrix_mulVec_eq_zero hx hadj
    have hconst : ∀ w, x w = x v₀ :=
      fun w => eq_const_of_adj_eq_connected (v₀ := v₀) (w := w) hconn hadj_eq
    exact ⟨x v₀, by
      ext w
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      exact (hconst w).symm⟩
  · rintro ⟨c, rfl⟩
    have h0 : (G.lapMatrix ℝ).mulVec (fun _ => (1 : ℝ)) = 0 := by
      ext v
      simp [SimpleGraph.lapMatrix_mulVec_apply']
    rw [mulVec_smul, h0]
    exact smul_zero c
end LapMatrixNullSpace
end Matrix
namespace EigenvalueBounds
open Matrix SimpleGraph Finset BigOperators Module.End


namespace EigenvalueBounds

/--
[eigenvalue_second_smallest_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Eigenvalues.lean)
-/
@[path]
lemma eigenvalue_second_smallest_pos
  [Fintype V]
  [DecidableEq V]
  (G : SimpleGraph V)
  [DecidableRel G.Adj]
-- given
  (hn : Fintype.card V ≥ 2)
  (hconn : G.Connected) :
-- imply
  let hL := isHermitian_lapMatrix ℝ G
  let n := Fintype.card V
  0 < hL.eigenvalues₀ ⟨n - 2, by omega⟩ := by
-- proof
  intro hL n
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hPSD := posSemidef_lapMatrix ℝ G
  have hnn : ∀ i, 0 ≤ hL.eigenvalues i := hPSD.eigenvalues_nonneg
  have hnn₀ : 0 ≤ hL.eigenvalues₀ ⟨n - 2, by omega⟩ := by
    have : hL.eigenvalues₀ ⟨n - 2, by omega⟩ =
      hL.eigenvalues ((Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨n - 2, by omega⟩) := by
      simp only [IsHermitian.eigenvalues, Equiv.symm_apply_apply]
    rw [this]
    exact hnn _
  suffices h : hL.eigenvalues₀ ⟨n - 2, by omega⟩ ≠ 0 from lt_of_le_of_ne hnn₀ (Ne.symm h)
  intro heq
  let j₁ := (Fintype.equivOfCardEq (Fintype.card_fin n)) ⟨n - 2, by omega⟩
  let j₂ := (Fintype.equivOfCardEq (Fintype.card_fin n)) ⟨n - 1, by omega⟩
  have hev₁ : hL.eigenvalues j₁ = 0 := by
    simp only [j₁, IsHermitian.eigenvalues, Equiv.symm_apply_apply]
    exact heq
  have hev₂ : hL.eigenvalues j₂ = 0 := by
    simp only [j₂, IsHermitian.eigenvalues, Equiv.symm_apply_apply]
    exact eigenvalues₀_min_eq_zero G
  have hker₁ : (G.lapMatrix ℝ).mulVec (hL.eigenvectorBasis j₁).1 = 0 := by
    have h := hL.mulVec_eigenvectorBasis j₁
    rwa [hev₁, zero_smul] at h
  have hker₂ : (G.lapMatrix ℝ).mulVec (hL.eigenvectorBasis j₂).1 = 0 := by
    have h := hL.mulVec_eigenvectorBasis j₂
    rwa [hev₂, zero_smul] at h
  have hspan := Matrix.lapMatrix_eigenspace_zero_eq_span_ones G hconn
  have hmem₁ : (hL.eigenvectorBasis j₁).1 ∈ Submodule.span ℝ {fun _ : V => (1 : ℝ)} := by
    rwa [← hspan, eigenspace_zero, LinearMap.mem_ker, mulVecLin_apply]
  have hmem₂ : (hL.eigenvectorBasis j₂).1 ∈ Submodule.span ℝ {fun _ : V => (1 : ℝ)} := by
    rwa [← hspan, eigenspace_zero, LinearMap.mem_ker, mulVecLin_apply]
  rw [Submodule.mem_span_singleton] at hmem₁ hmem₂
  obtain ⟨c₁, hc₁⟩ := hmem₁
  obtain ⟨c₂, hc₂⟩ := hmem₂
  have hne : j₁ ≠ j₂ := by
    intro h
    have := (Fintype.equivOfCardEq (Fintype.card_fin n)).injective h
    simp only [Fin.ext_iff] at this
    omega
  have horth : @inner ℝ _ _ (hL.eigenvectorBasis j₁) (hL.eigenvectorBasis j₂) = 0 :=
    hL.eigenvectorBasis.orthonormal.2 hne
  rw [PiLp.inner_apply] at horth
  simp only [← hc₁, ← hc₂, Pi.smul_apply, smul_eq_mul, mul_one] at horth
  simp only [inner, Inner.inner, RCLike.re_to_real] at horth
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at horth
  have hne₁ : (hL.eigenvectorBasis j₁ : EuclideanSpace ℝ V) ≠ 0 :=
    hL.eigenvectorBasis.toBasis.ne_zero j₁
  have hne₂ : (hL.eigenvectorBasis j₂ : EuclideanSpace ℝ V) ≠ 0 :=
    hL.eigenvectorBasis.toBasis.ne_zero j₂
  have hc₁_ne : c₁ ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc₁
    apply hne₁
    ext i
    exact congr_fun hc₁.symm i
  have hc₂_ne : c₂ ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc₂
    apply hne₂
    ext i
    exact congr_fun hc₂.symm i
  have hcard_ne : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero hcard_ne (mul_ne_zero hc₂_ne hc₁_ne) horth

end EigenvalueBounds

/--
[sum_eigenvalues](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Eigenvalues.lean)
-/
@[path]
private lemma sum_eigenvalues_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  let hL := isHermitian_lapMatrix ℝ G ∑ i, hL.eigenvalues₀ i = ∑ v : V, (G.degree v : ℝ) := by
-- proof
  apply EigenvalueBounds.sum_eigenvalues G

/--
[sum_eigenvalues](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Eigenvalues.lean)
-/
@[path]
private lemma sum_eigenvalues_eq_2
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  let hL := isHermitian_lapMatrix ℝ G (∑ i, hL.eigenvalues₀ i = ∑ v : V, (G.degree v : ℝ)) ∧ (∑ v : V, (G.degree v : ℝ)) ≤ (G.maxDegree : ℝ) * (Fintype.card V : ℝ) := by
-- proof
  apply EigenvalueBounds.sum_eigenvalues G

/--
[eigenvalues](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Eigenvalues.lean)
-/
@[path]
private lemma eigenvalues_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Nonempty V] :
-- imply
  let hL := isHermitian_lapMatrix ℝ G hL.eigenvalues₀ ⟨Fintype.card V - 1, Nat.sub_lt Fintype.card_pos Nat.one_pos⟩ = 0 := by
-- proof
  apply EigenvalueBounds.eigenvalues G


-- created on 2026-10-23
-- updated on 2026-10-28
