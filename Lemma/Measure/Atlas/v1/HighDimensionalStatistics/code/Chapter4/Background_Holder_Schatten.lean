import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Background_Holder_Schatten
open Matrix Real Finset


/--
[matrix_sum_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Background_Holder_Schatten.lean)
-/
@[path]
lemma matrix_sum_apply
  {d T : ℕ}
  [Fintype ι]
  {f : ι → Matrix (Fin d) (Fin T) ℝ}
  {i : Fin d}
  {j : Fin T} :
-- imply
  (∑ k, f k) i j = ∑ k, f k i j :=
-- proof
  congr_fun (Finset.sum_apply i Finset.univ f) j |>.trans
    (Finset.sum_apply j Finset.univ (fun k => f k i))

/--
[frobeniusInnerProduct_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Background_Holder_Schatten.lean)
-/
@[path]
lemma frobeniusInnerProduct_sum
  {d T : ℕ}
  [Fintype ι]
  {f : ι → Matrix (Fin d) (Fin T) ℝ}
  {B : Matrix (Fin d) (Fin T) ℝ} :
-- imply
  frobeniusInnerProduct (∑ k, f k) B = ∑ k, frobeniusInnerProduct (f k) B := by
-- proof
  simp only [frobeniusInnerProduct, matrix_sum_apply, Finset.sum_mul]
  simp_rw [show ∀ (a : Fin d), ∑ (b : Fin T), ∑ (c : ι), f c a b * B a b =
    ∑ (c : ι), ∑ (b : Fin T), f c a b * B a b from fun _ => Finset.sum_comm]
  exact Finset.sum_comm

/--
[frobeniusInnerProduct_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Background_Holder_Schatten.lean)
-/
@[path]
lemma frobeniusInnerProduct_smul
  {d T : ℕ}
  {c : ℝ}
  {A B : Matrix (Fin d) (Fin T) ℝ} :
-- imply
  frobeniusInnerProduct (c • A) B = c * frobeniusInnerProduct A B := by
-- proof
  simp only [frobeniusInnerProduct]
  rw [Finset.mul_sum]
  congr 1; ext i
  rw [Finset.mul_sum]
  congr 1; ext j
  simp [smul_eq_mul, mul_assoc]

/--
[frobeniusInnerProduct_vecMulVec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Background_Holder_Schatten.lean)
-/
@[path]
lemma frobeniusInnerProduct_vecMulVec
  {d T : ℕ}
  {u : Fin d → ℝ}
  {v : Fin T → ℝ}
  {B : Matrix (Fin d) (Fin T) ℝ} :
-- imply
  frobeniusInnerProduct (vecMulVec u v) B = dotProduct u (B.mulVec v) := by
-- proof
  simp only [frobeniusInnerProduct, vecMulVec, Matrix.of_apply, dotProduct, mulVec]
  congr 1; ext i
  simp only [Finset.mul_sum]
  congr 1; ext j; ring

/--
[dotProduct_mulVec_le_opNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Background_Holder_Schatten.lean)
-/
@[path]
lemma dotProduct_mulVec_le_opNorm
  {d T : ℕ}
  {u : Fin d → ℝ}
  {v : Fin T → ℝ}
  {B : Matrix (Fin d) (Fin T) ℝ}
-- given
  (hu : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ = 1)
  (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin T))‖ = 1) :
-- imply
  dotProduct u (B.mulVec v) ≤ matrixOpNorm B := by
-- proof
  let u_euc : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 u
  let v_euc : EuclideanSpace ℝ (Fin T) := WithLp.toLp 2 v
  have h1 : dotProduct u (B.mulVec v) =
    @inner ℝ _ _ u_euc (toEuclideanLin B v_euc) := by
    simp [inner, dotProduct, toEuclideanLin, toLpLin, mulVec, u_euc, v_euc]
    congr 1; ext i; ring
  rw [h1]
  calc @inner ℝ _ _ u_euc (toEuclideanLin B v_euc)
    ≤ ‖u_euc‖ * ‖toEuclideanLin B v_euc‖ := real_inner_le_norm u_euc _
    _ = ‖u_euc‖ * ‖(toEuclideanLin B).toContinuousLinearMap v_euc‖ := by
      simp [LinearMap.toContinuousLinearMap]
    _ ≤ ‖u_euc‖ * (‖(toEuclideanLin B).toContinuousLinearMap‖ * ‖v_euc‖) := by
      gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = matrixOpNorm B := by rw [hu, hv]; simp [matrixOpNorm]

/--
[extendedσval_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Background_Holder_Schatten.lean)
-/
@[path]
lemma extendedσval_nonneg {d T : ℕ} (S : SVD d T) (j : Fin (min d T)) :
  0 ≤ extendedσval S j := by
  simp only [extendedσval]; split_ifs with h
  · exact S.σval_nonneg _
  · exact le_refl _

/--
[sum_fin_of_zero_tail](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Background_Holder_Schatten.lean)
-/
@[path]
lemma sum_fin_of_zero_tail
  {r n : ℕ}
  {f : Fin n → ℝ}
-- given
  (hr : r ≤ n)
  (hf : ∀ j : Fin n, r ≤ j.val → f j = 0) :
-- imply
  ∑ j : Fin n, f j = ∑ j : Fin r, f ⟨j.val, by omega⟩ := by
-- proof
  classical
  have key : ∀ j : Fin n, f j = if j.val < r then f j else 0 := by
    intro j
    split_ifs with h
    · rfl
    · exact hf j (by omega)
  conv_lhs =>
    arg 2; ext j; rw [key j]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  symm
  apply Finset.sum_nbij (fun (j : Fin r) => (⟨j.val, by omega⟩ : Fin n))
  · intro j _; simp [j.isLt]
  · intro a b _ _ h; exact Fin.ext (Fin.mk.inj h)
  · intro b hb
    simp at hb
    exact ⟨⟨b.val, hb⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro a ha; rfl

/--
[sum_extendedσval_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Background_Holder_Schatten.lean)
-/
@[path]
over the original `Fin S.r` singular values. -/
lemma sum_extendedσval_rpow {d T : ℕ} (S : SVD d T) (p : ℝ) (hp : 0 < p) :
  ∑ j : Fin (min d T), (extendedσval S j) ^ p =
  ∑ j : Fin S.r, (S.σval j) ^ p := by
  rw [sum_fin_of_zero_tail S.hr]
  · congr 1; ext j; simp [extendedσval, j.isLt]
  · intro j hj
    simp [extendedσval, show ¬(j.val < S.r) from by omega, hp.ne']

/--
[holderConjugate_of_div_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Background_Holder_Schatten.lean)
-/
@[path]
lemma holderConjugate_of_div_add
  {p q : ℝ}
-- given
  (hp : 1 ≤ p)
  (hq : 1 ≤ q)
  (hpq : 1 / p + 1 / q = 1) :
-- imply
  p.HolderConjugate q := by
-- proof
  rw [Real.holderConjugate_iff]
  constructor
  · by_contra h
    push Not at h
    have hpe : p = 1 := le_antisymm h hp
    subst hpe; simp at hpq; linarith
  · rwa [one_div, one_div] at hpq

/--
[holder_schatten_nuclear_op](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Background_Holder_Schatten.lean)
-/
@[path]
lemma holder_schatten_nuclear_op
  {d T : ℕ}
  {A B : Matrix (Fin d) (Fin T) ℝ}
  {S_A : SVD d T}
-- given
  (hA : S_A.IsDecompOf A)
  (hu : ∀ j, ‖(WithLp.toLp 2 (S_A.u j) : EuclideanSpace ℝ (Fin d))‖ = 1)
  (hv : ∀ j, ‖(WithLp.toLp 2 (S_A.v j) : EuclideanSpace ℝ (Fin T))‖ = 1) :
-- imply
  frobeniusInnerProduct A B ≤ nuclearNormSVD S_A * matrixOpNorm B := by
-- proof
  rw [hA, SVD.toMatrix]
  rw [frobeniusInnerProduct_sum]
  simp_rw [frobeniusInnerProduct_smul, frobeniusInnerProduct_vecMulVec]
  rw [nuclearNormSVD, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left
    (dotProduct_mulVec_le_opNorm _ _ B (hu k) (hv k))
    (S_A.σval_nonneg k)
/-- **General Hölder inequality for Schatten norms.** For Hölder conjugate exponents
$1/p + 1/q = 1$, $|\langle A, B\rangle_F| \le \|A\|_{S_p} \cdot \|B\|_{S_q}$. -/

/--
[extended](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Background_Holder_Schatten.lean)
-/
@[path]
private lemma extended_eq
  {d T : ℕ}
  {S : SVD d T}
  {j : Fin (min d T)} :
-- imply
  0 ≤ extendedσval S j := by
-- proof
  apply extended S j

/--
[sum_extended](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Background_Holder_Schatten.lean)
-/
@[path]
private lemma sum_extended_eq
  {d T : ℕ}
  {S : SVD d T}
  {p : ℝ}
-- given
  (hp : 0 < p) :
-- imply
  ∑ j : Fin (min d T), (extendedσval S j) ^ p = ∑ j : Fin S.r, (S.σval j) ^ p := by
-- proof
  apply sum_extended S p hp


-- created on 2026-10-23
