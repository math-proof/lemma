import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_8
open Matrix Real Thm48


namespace Thm48

/--
[theorem_4_8_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma theorem_4_8_left
  {d : ℕ}
  {vtilde v : EuclideanSpace ℝ (Fin d)}
-- given
  (hvt : ‖vtilde‖ = 1)
  (hv : ‖v‖ = 1) :
-- imply
  min (‖vtilde - v‖ ^ 2) (‖vtilde + v‖ ^ 2) ≤ 2 * Real.sin (principalAngle vtilde v) ^ 2 := by
-- proof
  set c := @inner ℝ _ _ vtilde v with hc_def
  have h_sub : ‖vtilde - v‖ ^ 2 = 2 - 2 * c := by
    rw [norm_sub_sq_real]; rw [hvt, hv]; ring
  have h_add : ‖vtilde + v‖ ^ 2 = 2 + 2 * c := by
    rw [norm_add_sq_real]; rw [hvt, hv]; ring
  have h_abs_le : |c| ≤ 1 := by
    have := abs_real_inner_le_norm vtilde v
    rw [hvt, hv] at this; linarith
  have h_sin : Real.sin (principalAngle vtilde v) = Real.sqrt (1 - |c| ^ 2) := by
    unfold principalAngle; rw [hc_def]; exact Real.sin_arccos |c|
  have h_sin_sq : Real.sin (principalAngle vtilde v) ^ 2 = 1 - |c| ^ 2 := by
    rw [h_sin, sq_sqrt]; nlinarith [sq_abs c, sq_nonneg (1 - |c|)]
  rw [h_sin_sq, h_sub, h_add]
  have h_abs_nn : 0 ≤ |c| := abs_nonneg c
  have h_sq_le : |c| ^ 2 ≤ |c| := by nlinarith [sq_abs c]
  have h_min_le : min (2 - 2 * c) (2 + 2 * c) ≤ 2 - 2 * |c| := by
    by_cases hc : 0 ≤ c
    · rw [abs_of_nonneg hc]; exact min_le_left _ _
    · push_neg at hc
      rw [abs_of_neg hc]
      simp only [mul_neg, sub_neg_eq_add]
      linarith [min_le_right (2 - 2 * c) (2 + 2 * c)]
  linarith

end Thm48

namespace Thm48

/--
[smul_mulVec_distrib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma smul_mulVec_distrib
  {d : ℕ}
  {θ : ℝ}
  {M : Matrix (Fin d) (Fin d) ℝ}
  {u : Fin d → ℝ} :
-- imply
  (θ • M).mulVec u = θ • (M.mulVec u) := by
-- proof
  ext i; simp [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1; ext j; ring

end Thm48

namespace Thm48

/--
[vecMulVec_self_mulVec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma vecMulVec_self_mulVec
  {d : ℕ}
  {v x : Fin d → ℝ} :
-- imply
  (vecMulVec v v).mulVec x = (dotProduct v x) • v := by
-- proof
  ext i; simp [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf; rw [Finset.mul_sum]; congr 1; ext j; ring

end Thm48

namespace Thm48

/--
[dotProduct_vecMulVec_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma dotProduct_vecMulVec_self
  {d : ℕ}
  {v x : Fin d → ℝ} :
-- imply
  dotProduct x ((vecMulVec v v).mulVec x) = (dotProduct v x) ^ 2 := by
-- proof
  rw [vecMulVec_self_mulVec, dotProduct_smul, sq, dotProduct_comm x v]
  simp [smul_eq_mul]

end Thm48

namespace Thm48

/--
[rayleigh_spiked_model](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma rayleigh_spiked_model
  {d : ℕ}
  {θ : ℝ}
  {v u : Fin d → ℝ} :
-- imply
  dotProduct u ((θ • vecMulVec v v + (1 : Matrix (Fin d) (Fin d) ℝ)).mulVec u) = θ * (dotProduct v u) ^ 2 + dotProduct u u := by
-- proof
  rw [add_mulVec, smul_mulVec_distrib, one_mulVec, dotProduct_add,
    dotProduct_smul, dotProduct_vecMulVec_self]
  simp [smul_eq_mul]

end Thm48

namespace Thm48

/--
[dotProduct_self_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma dotProduct_self_unit
  {d : ℕ}
  {u : EuclideanSpace ℝ (Fin d)}
-- given
  (hu : ‖u‖ = 1) :
-- imply
  dotProduct (EuclideanSpace.equiv (Fin d) ℝ u) (EuclideanSpace.equiv (Fin d) ℝ u) = 1 := by
-- proof
  show u.ofLp ⬝ᵥ u.ofLp = 1
  have h1 : @inner ℝ _ _ u u = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
  have h2 := EuclideanSpace.inner_eq_star_dotProduct u u; simp [star_trivial] at h2
  rw [hu] at h1; linarith [h2.symm.trans h1]

end Thm48

namespace Thm48

/--
[inner_eq_dotProduct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma inner_eq_dotProduct
  {d : ℕ}
  {u v : EuclideanSpace ℝ (Fin d)} :
-- imply
  @inner ℝ _ _ u v = dotProduct (EuclideanSpace.equiv (Fin d) ℝ u) (EuclideanSpace.equiv (Fin d) ℝ v) :=
-- proof
  (EuclideanSpace.inner_eq_star_dotProduct u v).trans
    (by simp [star_trivial]; exact dotProduct_comm _ _)

end Thm48

namespace Thm48

/--
[toEuclideanLin_ofLp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma toEuclideanLin_ofLp
  {d : ℕ}
  {A : Matrix (Fin d) (Fin d) ℝ}
  {x : EuclideanSpace ℝ (Fin d)} :
-- imply
  (toEuclideanLin A x).ofLp = A.mulVec x.ofLp := by
-- proof
  simp [toEuclideanLin, toLpLin, LinearEquiv.trans_apply,
    LinearEquiv.arrowCongr_apply, WithLp.linearEquiv_symm_apply, toLin'_apply]

end Thm48

namespace Thm48

/--
[inner_toEuclideanLin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma inner_toEuclideanLin
  {d : ℕ}
  {A : Matrix (Fin d) (Fin d) ℝ}
  {x : EuclideanSpace ℝ (Fin d)} :
-- imply
  @inner ℝ _ _ (toEuclideanLin A x) x = dotProduct x.ofLp (A.mulVec x.ofLp) := by
-- proof
  have h_inner : @inner ℝ _ _ (toEuclideanLin A x) x =
    x.ofLp ⬝ᵥ (toEuclideanLin A x).ofLp :=
    (EuclideanSpace.inner_eq_star_dotProduct (toEuclideanLin A x) x).trans
      (by simp [star_trivial])
  rw [h_inner, toEuclideanLin_ofLp]

end Thm48

namespace Thm48

/--
[symmetric_dotProduct_mulVec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma symmetric_dotProduct_mulVec
  {d : ℕ}
  {M : Matrix (Fin d) (Fin d) ℝ}
  {u w : Fin d → ℝ}
-- given
  (hM : Mᵀ = M) :
-- imply
  dotProduct u (M.mulVec w) = dotProduct w (M.mulVec u) := by
-- proof
  rw [dotProduct_mulVec u M, ← mulVec_transpose M u]
  rw [hM]
  exact dotProduct_comm (M.mulVec u) w

end Thm48

namespace Thm48

/--
[bilinear_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma bilinear_identity
  {d : ℕ}
  {M : Matrix (Fin d) (Fin d) ℝ}
  {u w : Fin d → ℝ}
-- given
  (hM : Mᵀ = M) :
-- imply
  dotProduct u (M.mulVec u) - dotProduct w (M.mulVec w) = dotProduct (u - w) (M.mulVec (u + w)) := by
-- proof
  have hsym := symmetric_dotProduct_mulVec M hM u w
  simp only [mulVec_add, dotProduct_add, sub_dotProduct]
  linarith

end Thm48

namespace Thm48

/--
[inner_toEuclideanLin'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma inner_toEuclideanLin'
  {d : ℕ}
  {A : Matrix (Fin d) (Fin d) ℝ}
  {u w : EuclideanSpace ℝ (Fin d)} :
-- imply
  @inner ℝ _ _ u (toEuclideanLin A w) = dotProduct u.ofLp (A.mulVec w.ofLp) := by
-- proof
  rw [inner_eq_dotProduct u (toEuclideanLin A w)]
  show u.ofLp ⬝ᵥ (toEuclideanLin A w).ofLp = u.ofLp ⬝ᵥ A *ᵥ w.ofLp
  rw [toEuclideanLin_ofLp]
set_option maxHeartbeats 800000 in

end Thm48

namespace Thm48

/--
[abs_bilinear_le_opNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma abs_bilinear_le_opNorm
  {d : ℕ}
  {A : Matrix (Fin d) (Fin d) ℝ}
  {u w : EuclideanSpace ℝ (Fin d)} :
-- imply
  |dotProduct u.ofLp (A.mulVec w.ofLp)| ≤ ‖u‖ * matrixOpNorm A * ‖w‖ := by
-- proof
  rw [← inner_toEuclideanLin']
  set f := (toEuclideanLin A).toContinuousLinearMap
  have h_eq : toEuclideanLin A w = f w := rfl
  rw [h_eq]
  calc |@inner ℝ _ _ u (f w)|
    ≤ ‖u‖ * ‖f w‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖f‖ * ‖w‖) := by
      apply mul_le_mul_of_nonneg_left (f.le_opNorm w) (norm_nonneg _)
    _ = ‖u‖ * matrixOpNorm A * ‖w‖ := by unfold matrixOpNorm; ring

end Thm48

namespace Thm48

/--
[spiked_transpose_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma spiked_transpose_eq
  {d : ℕ}
  {θ : ℝ}
  {v : EuclideanSpace ℝ (Fin d)} :
-- imply
  (θ • vecMulVec v v + (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ = θ • vecMulVec v v + (1 : Matrix (Fin d) (Fin d) ℝ) := by
-- proof
  rw [transpose_add, transpose_smul]
  congr 1
  · congr 1; ext i j; simp [vecMulVec_apply]; ring
  · exact transpose_one
set_option maxHeartbeats 1600000 in

end Thm48

namespace Thm48

/--
[davis_kahan_sin_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma davis_kahan_sin_bound
  {d : ℕ}
  {Sig : Matrix (Fin d) (Fin d) ℝ}
  {θ : ℝ}
  {v : EuclideanSpace ℝ (Fin d)}
  {SigTilde : Matrix (Fin d) (Fin d) ℝ}
  {vtilde : EuclideanSpace ℝ (Fin d)}
-- given
  (hSpike : IsSpikedCovariance Sig θ v)
  (hPSD : SigTilde.PosSemidef)
  (hvt : ‖vtilde‖ = 1)
  (hEig : IsLargestEigenvector SigTilde vtilde) :
-- imply
  Real.sin (principalAngle vtilde v) ≤ 2 / θ * matrixOpNorm (SigTilde - Sig) := by
-- proof
  obtain ⟨hθ, hv, hSig⟩ := hSpike
  set c := @inner ℝ _ _ vtilde v
  set vf := EuclideanSpace.equiv (Fin d) ℝ v
  set vtf := EuclideanSpace.equiv (Fin d) ℝ vtilde
  have hvf_eq : v.ofLp = vf := rfl
  have hvtf_eq : vtilde.ofLp = vtf := rfl
  have h_abs_le : |c| ≤ 1 := by
    have := abs_real_inner_le_norm vtilde v; rw [hvt, hv] at this; linarith
  have h_sin : Real.sin (principalAngle vtilde v) = Real.sqrt (1 - |c| ^ 2) := by
    unfold principalAngle; exact Real.sin_arccos |c|
  have h_sin_nn : 0 ≤ Real.sin (principalAngle vtilde v) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (arccos_nonneg _) (arccos_le_pi _)
  have h_rv : dotProduct vf (Sig.mulVec vf) = 1 + θ := by
    rw [hSig, rayleigh_spiked_model]
    have hdp := dotProduct_self_unit v hv
    have hvf : dotProduct vf vf = 1 := hdp
    rw [← hvf_eq]; rw [hvf_eq]; rw [hvf]; ring
  have h_rvt : dotProduct vtf (Sig.mulVec vtf) = 1 + θ * c ^ 2 := by
    rw [hSig, rayleigh_spiked_model, dotProduct_self_unit vtilde hvt]
    have h_inner_vvt := inner_eq_dotProduct vtilde v
    change c = dotProduct vtf vf at h_inner_vvt
    have hvc : v.ofLp ⬝ᵥ vtf = c := by
      rw [hvf_eq, dotProduct_comm, ← h_inner_vvt]
    rw [hvc]; ring
  have h_diff : dotProduct vf (Sig.mulVec vf) - dotProduct vtf (Sig.mulVec vtf) =
    θ * (1 - c ^ 2) := by rw [h_rv, h_rvt]; ring
  have h_eig_ineq := hEig.2 v hv
  set Δ := SigTilde - Sig
  have hSigSym : Sigᵀ = Sig := by rw [hSig]; exact spiked_transpose_eq θ v
  have hSTSym : SigTildeᵀ = SigTilde := by
    have h := hPSD.1
    exact_mod_cast h
  have hΔsym : Δᵀ = Δ := by
    show (SigTilde - Sig)ᵀ = SigTilde - Sig
    rw [transpose_sub, hSTSym, hSigSym]
  have h_decomp_v : dotProduct vf (SigTilde.mulVec vf) =
    dotProduct vf (Sig.mulVec vf) + dotProduct vf (Δ.mulVec vf) := by
    have : SigTilde = Sig + Δ := by simp [Δ]
    rw [this, add_mulVec, dotProduct_add]
  have h_decomp_vt : dotProduct vtf (SigTilde.mulVec vtf) =
    dotProduct vtf (Sig.mulVec vtf) + dotProduct vtf (Δ.mulVec vtf) := by
    have : SigTilde = Sig + Δ := by simp [Δ]
    rw [this, add_mulVec, dotProduct_add]
  have h_rayleigh_bound : θ * (1 - c ^ 2) ≤
    dotProduct vtf (Δ.mulVec vtf) - dotProduct vf (Δ.mulVec vf) := by
    rw [h_decomp_v, h_decomp_vt] at h_eig_ineq
    linarith [h_diff]
  have h_bilinear : dotProduct vtf (Δ.mulVec vtf) - dotProduct vf (Δ.mulVec vf) =
    dotProduct (vtf - vf) (Δ.mulVec (vtf + vf)) :=
    bilinear_identity Δ hΔsym vtf vf
  have h_cs_bound : dotProduct (vtf - vf) (Δ.mulVec (vtf + vf)) ≤
    ‖vtilde - v‖ * matrixOpNorm Δ * ‖vtilde + v‖ := by
    calc dotProduct (vtf - vf) (Δ.mulVec (vtf + vf))
      ≤ |dotProduct (vtf - vf) (Δ.mulVec (vtf + vf))| := le_abs_self _
      _ ≤ ‖vtilde - v‖ * matrixOpNorm Δ * ‖vtilde + v‖ :=
        abs_bilinear_le_opNorm Δ (vtilde - v) (vtilde + v)
  have h_norm_sub_sq : ‖vtilde - v‖ ^ 2 = 2 - 2 * c := by
    rw [norm_sub_sq_real, hvt, hv]; ring
  have h_norm_add_sq : ‖vtilde + v‖ ^ 2 = 2 + 2 * c := by
    rw [norm_add_sq_real, hvt, hv]; ring
  have h_sin_sq : Real.sin (principalAngle vtilde v) ^ 2 = 1 - c ^ 2 := by
    rw [h_sin, sq_sqrt (by nlinarith [sq_abs c, sq_nonneg (1 - |c|)])]
    congr 1; rw [sq_abs]
  have h_norm_prod_sq : ‖vtilde - v‖ ^ 2 * ‖vtilde + v‖ ^ 2 =
    4 * Real.sin (principalAngle vtilde v) ^ 2 := by
    rw [h_norm_sub_sq, h_norm_add_sq, h_sin_sq]; ring
  have h_norm_sub_nn : 0 ≤ ‖vtilde - v‖ := norm_nonneg _
  have h_norm_add_nn : 0 ≤ ‖vtilde + v‖ := norm_nonneg _
  have h_op_nn : 0 ≤ matrixOpNorm Δ := norm_nonneg _
  by_cases hs : Real.sin (principalAngle vtilde v) = 0
  · rw [hs]; positivity
  ·
    have h_sin_pos : 0 < Real.sin (principalAngle vtilde v) :=
      lt_of_le_of_ne h_sin_nn (Ne.symm hs)
    have h_combined : θ * (1 - c ^ 2) ≤
      ‖vtilde - v‖ * matrixOpNorm Δ * ‖vtilde + v‖ := by
      linarith [h_rayleigh_bound, h_bilinear, h_cs_bound]
    have h_norm_prod : ‖vtilde - v‖ * ‖vtilde + v‖ =
      2 * Real.sin (principalAngle vtilde v) := by
      have h1 : (‖vtilde - v‖ * ‖vtilde + v‖) ^ 2 =
        (2 * Real.sin (principalAngle vtilde v)) ^ 2 := by
        rw [mul_pow, mul_pow]; linarith [h_norm_prod_sq]
      have h_lhs_nn : 0 ≤ ‖vtilde - v‖ * ‖vtilde + v‖ :=
        mul_nonneg h_norm_sub_nn h_norm_add_nn
      have h_rhs_nn : 0 ≤ 2 * Real.sin (principalAngle vtilde v) := by positivity
      nlinarith [sq_nonneg (‖vtilde - v‖ * ‖vtilde + v‖ - 2 * Real.sin (principalAngle vtilde v))]
    rw [h_sin_sq.symm] at h_combined
    have h_final : θ * Real.sin (principalAngle vtilde v) ^ 2 ≤
      2 * Real.sin (principalAngle vtilde v) * matrixOpNorm Δ := by
      have : ‖vtilde - v‖ * matrixOpNorm Δ * ‖vtilde + v‖ =
        (‖vtilde - v‖ * ‖vtilde + v‖) * matrixOpNorm Δ := by ring
      rw [this, h_norm_prod] at h_combined
      linarith
    have h_div : θ * Real.sin (principalAngle vtilde v) ≤ 2 * matrixOpNorm Δ := by
      rw [sq] at h_final
      have h_ineq : θ * Real.sin (principalAngle vtilde v) * Real.sin (principalAngle vtilde v) ≤
        2 * matrixOpNorm Δ * Real.sin (principalAngle vtilde v) := by linarith
      exact le_of_mul_le_mul_right h_ineq h_sin_pos
    rw [div_mul_eq_mul_div, le_div_iff₀ hθ]
    linarith

end Thm48

namespace Thm48

/--
[theorem_4_8_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma theorem_4_8_right
  {d : ℕ}
  {Sig : Matrix (Fin d) (Fin d) ℝ}
  {θ : ℝ}
  {v : EuclideanSpace ℝ (Fin d)}
  {SigTilde : Matrix (Fin d) (Fin d) ℝ}
  {vtilde : EuclideanSpace ℝ (Fin d)}
-- given
  (hSpike : IsSpikedCovariance Sig θ v)
  (hPSD : SigTilde.PosSemidef)
  (hvt : ‖vtilde‖ = 1)
  (hEig : IsLargestEigenvector SigTilde vtilde) :
-- imply
  2 * Real.sin (principalAngle vtilde v) ^ 2 ≤ 8 / θ ^ 2 * matrixOpNorm (SigTilde - Sig) ^ 2 := by
-- proof
  obtain ⟨hθ, hv, _⟩ := hSpike
  have hSpike' : IsSpikedCovariance Sig θ v := ⟨hθ, hv, by assumption⟩
  have h_key := davis_kahan_sin_bound Sig θ v hSpike' SigTilde hPSD vtilde hvt hEig
  have h_sin_nn : 0 ≤ Real.sin (principalAngle vtilde v) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (arccos_nonneg _) (arccos_le_pi _)
  have h_op_nn : 0 ≤ matrixOpNorm (SigTilde - Sig) := norm_nonneg _
  have h1 : Real.sin (principalAngle vtilde v) ^ 2 ≤
    (2 / θ * matrixOpNorm (SigTilde - Sig)) ^ 2 :=
    sq_le_sq' (by linarith) h_key
  calc 2 * Real.sin (principalAngle vtilde v) ^ 2
    ≤ 2 * (2 / θ * matrixOpNorm (SigTilde - Sig)) ^ 2 := by linarith
    _ = 8 / θ ^ 2 * matrixOpNorm (SigTilde - Sig) ^ 2 := by ring

end Thm48

namespace Thm48

/--
[theorem_4_8](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean)
-/
@[path]
lemma theorem_4_8
  {d : ℕ}
  {Sig : Matrix (Fin d) (Fin d) ℝ}
  {θ : ℝ}
  {v : EuclideanSpace ℝ (Fin d)}
  {SigTilde : Matrix (Fin d) (Fin d) ℝ}
  {vtilde : EuclideanSpace ℝ (Fin d)}
-- given
  (hSpike : IsSpikedCovariance Sig θ v)
  (hPSD : SigTilde.PosSemidef)
  (hvt : ‖vtilde‖ = 1)
  (hEig : IsLargestEigenvector SigTilde vtilde) :
-- imply
  min (‖vtilde - v‖ ^ 2) (‖vtilde + v‖ ^ 2) ≤ 8 / θ ^ 2 * matrixOpNorm (SigTilde - Sig) ^ 2 := by
-- proof
  have hv : ‖v‖ = 1 := hSpike.2.1
  have hL := theorem_4_8_left vtilde v hvt hv
  have hR := theorem_4_8_right Sig θ v hSpike SigTilde hPSD vtilde hvt hEig
  linarith

end Thm48


-- created on 2026-10-23
