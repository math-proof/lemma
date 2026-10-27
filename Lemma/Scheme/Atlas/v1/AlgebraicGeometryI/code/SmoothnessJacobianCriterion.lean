import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SmoothnessJacobianCriterion.Part3


/--
[matrix_fin1_rank_eq_one_iff_SJC](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessJacobianCriterion.lean)
-/
@[path]
lemma matrix_fin1_rank_eq_one_iff_SJC
  [Field k]
  {n : ℕ}
  {M : Matrix (Fin 1) (Fin n) k} :
-- imply
  M.rank = 1 ↔ ∃ j, M 0 j ≠ 0 := by
-- proof
  constructor
  · intro h
    by_contra h_all
    push Not at h_all
    have hM : M = 0 := by ext i j; fin_cases i; exact h_all j
    have : M.rank = 0 := by rw [hM]; simp [Matrix.rank]
    omega
  · intro ⟨j, hj⟩
    have hne : M ≠ 0 := by
      intro heq; apply hj; have := congr_fun (congr_fun heq 0) j; exact this
    have hle : M.rank ≤ 1 := by
      calc M.rank ≤ Fintype.card (Fin 1) := Matrix.rank_le_card_height M
        _ = 1 := by simp
    have hpos : 0 < M.rank := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      apply hne
      unfold Matrix.rank at h0
      rw [Submodule.finrank_eq_zero] at h0
      rw [LinearMap.range_eq_bot] at h0
      ext i j
      have hcol := congr_fun (LinearMap.ext_iff.mp h0 (Pi.single j 1)) i
      simp [Matrix.mulVecLin, Matrix.mulVec_single] at hcol
      exact hcol
    omega

/--
[corollary23_hypersurface_criterion_SJC](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessJacobianCriterion.lean)
-/
@[path]
lemma corollary23_hypersurface_criterion_SJC
  [Field k]
  {n : ℕ}
  {P : MvPolynomial (Fin n) k}
  {x : Fin n → k}
-- given
  (_hx : MvPolynomial.eval x P = 0) :
-- imply
  (∃ i : Fin n, MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0) ↔ (jacobianMatrix_SJC (fun _ : Fin 1 => P) x).rank = 1 := by
-- proof
  rw [matrix_fin1_rank_eq_one_iff_SJC]
  simp only [jacobianMatrix_SJC]
/-- **Smoothness criterion for hypersurfaces (Corollary 23)**: a hypersurface
`V(P)` of dimension `n - 1` is smooth at `x` iff some partial derivative of `P`
is non-zero at `x` — the classical "gradient is non-zero" criterion. -/


-- created on 2026-10-23
