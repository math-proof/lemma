import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.ODE.LinearSystemFundamentalMatrix
open MeasureTheory
open MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted


namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

/--
[fundMatrix_exists_operator_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma fundMatrix_exists_operator_bound
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (a b : ℝ) :
  ∃ L : NNReal, ∀ t ∈ Set.Icc a b, ‖B t‖₊ ≤ L := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hB.continuousOn
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  intro t ht
  change ‖B t‖ ≤ max C 0
  exact (hC t ht).trans (le_max_left _ _)

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

/--
[fundMatrix_linear_uniqueOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma fundMatrix_linear_uniqueOn
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t₀ r : ℝ) (hr : 0 < r)
  {x y : ℝ → E}
  (hx : ∀ t ∈ Set.Ioo (t₀ - r) (t₀ + r), HasDerivAt x (B t (x t)) t)
  (hy : ∀ t ∈ Set.Ioo (t₀ - r) (t₀ + r), HasDerivAt y (B t (y t)) t)
  (hxy : x t₀ = y t₀) :
  Set.EqOn x y (Set.Ioo (t₀ - r) (t₀ + r)) := by
  obtain ⟨L, hL⟩ := fundMatrix_exists_operator_bound B hB (t₀ - r) (t₀ + r)
  apply ODE_solution_unique_of_mem_Ioo
    (v := fun t z ↦ B t z) (s := fun _ ↦ Set.univ) (K := L) (t₀ := t₀)
  · intro t ht
    exact ((B t).lipschitzWith.weaken (hL t (Set.Ioo_subset_Icc_self ht))).lipschitzOnWith
  · simp [hr]
  · exact fun t ht ↦ ⟨hx t ht, Set.mem_univ _⟩
  · exact fun t ht ↦ ⟨hy t ht, Set.mem_univ _⟩
  · exact hxy

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

/--
[fundMatrix_clampedSolution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma fundMatrix_clampedSolution
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t₀ : ℝ) (x₀ : E) (N : ℕ) :
  ∃! x : ℝ → E, x t₀ = x₀ ∧ ∀ t,
    HasDerivAt x (B (Set.projIcc (t₀ - N) (t₀ + N) (by
      have := Nat.cast_nonneg (α := ℝ) N
      linarith) t) (x t)) t := by
  let c : ℝ → ℝ := fun t ↦ Set.projIcc (t₀ - N) (t₀ + N) (by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith) t
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  obtain ⟨L, hL⟩ :=
    fundMatrix_exists_operator_bound B hB (t₀ - N) (t₀ + N)
  apply MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
    (fun t x ↦ B (c t) x) t₀ x₀ L
  · change Continuous (fun p : ℝ × E ↦ B (c p.1) p.2)
    exact (hB.comp (hc.comp continuous_fst)).clm_apply continuous_snd
  · intro t
    apply (B (c t)).lipschitzWith.weaken
    exact hL _ (Set.projIcc (t₀ - N) (t₀ + N) (by
      have := Nat.cast_nonneg (α := ℝ) N
      linarith) t).property

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

/--
[fundMatrix_clampedAgree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma fundMatrix_clampedAgree
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t₀ : ℝ)
  {x y : ℝ → E} {N M : ℕ}
  (hx : x t₀ = y t₀ ∧ ∀ t, HasDerivAt x
    (B (Set.projIcc (t₀ - N) (t₀ + N) (by
      have := Nat.cast_nonneg (α := ℝ) N
      linarith) t) (x t)) t)
  (hy : ∀ t, HasDerivAt y
    (B (Set.projIcc (t₀ - M) (t₀ + M) (by
      have := Nat.cast_nonneg (α := ℝ) M
      linarith) t) (y t)) t)
  {t : ℝ} (hN : |t - t₀| < N) (hM : |t - t₀| < M) : x t = y t := by
  let r : ℝ := min N M
  have htr : |t - t₀| < r := lt_min hN hM
  have hr : 0 < r := (abs_nonneg _).trans_lt htr
  apply fundMatrix_linear_uniqueOn B hB t₀ r hr (x := x) (y := y) _ _ hx.1
    (show t ∈ Set.Ioo (t₀ - r) (t₀ + r) by rw [abs_lt] at htr; constructor <;> linarith)
  · intro s hs
    have hsN : s ∈ Set.Icc (t₀ - N) (t₀ + N) := by
      dsimp [r] at hs
      constructor <;> linarith [hs.1, hs.2, min_le_left (N : ℝ) M]
    simpa [Set.projIcc_of_mem _ hsN] using hx.2 s
  · intro s hs
    have hsM : s ∈ Set.Icc (t₀ - M) (t₀ + M) := by
      dsimp [r] at hs
      constructor <;> linarith [hs.1, hs.2, min_le_right (N : ℝ) M]
    simpa [Set.projIcc_of_mem _ hsM] using hy s

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

/--
[existsUnique_hasDerivAt_eq_continuousLinearMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
has a unique global integral curve through every initial point. -/
lemma _root_.ODE.existsUnique_hasDerivAt_eq_continuousLinearMap
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (B : ℝ → E →L[ℝ] E) (t₀ : ℝ) (x₀ : E) (hB : Continuous B) :
  ∃! x : ℝ → E, x t₀ = x₀ ∧ ∀ t, HasDerivAt x (B t (x t)) t := by
  classical
  let sol : ℕ → ℝ → E := fun N ↦
    Classical.choose (fundMatrix_clampedSolution B hB t₀ x₀ N).exists
  have hsol (N : ℕ) : sol N t₀ = x₀ ∧ ∀ t, HasDerivAt (sol N)
    (B (Set.projIcc (t₀ - N) (t₀ + N) (by
      have := Nat.cast_nonneg (α := ℝ) N
      linarith) t) (sol N t)) t :=
    Classical.choose_spec (fundMatrix_clampedSolution B hB t₀ x₀ N).exists
  let radius : ℝ → ℕ := fun t ↦ Classical.choose (exists_nat_gt |t - t₀|)
  have hradius (t : ℝ) : |t - t₀| < radius t :=
    Classical.choose_spec (exists_nat_gt |t - t₀|)
  let x : ℝ → E := fun t ↦ sol (radius t) t
  have hx₀ : x t₀ = x₀ := by
    change sol (radius t₀) t₀ = x₀
    exact (hsol _).1
  have hx (t : ℝ) : HasDerivAt x (B t (x t)) t := by
    obtain ⟨N, hN⟩ := exists_nat_gt (|t - t₀| + 1)
    have htN : |t - t₀| < (N : ℝ) := lt_trans (lt_add_one _) hN
    have hevent : ∀ᶠ u in nhds t, |u - t₀| < (N : ℝ) :=
      (continuousAt_id.sub continuousAt_const).abs.eventually_lt continuousAt_const htN
    have heq : x =ᶠ[nhds t] sol N := by
      filter_upwards [hevent] with u hu
      exact fundMatrix_clampedAgree B hB t₀
        ⟨(hsol (radius u)).1.trans (hsol N).1.symm, (hsol (radius u)).2⟩
        (hsol N).2 (hradius u) hu
    have htIcc : t ∈ Set.Icc (t₀ - N) (t₀ + N) := by
      rw [abs_lt] at htN
      constructor <;> linarith
    have hd := (hsol N).2 t
    rw [Set.projIcc_of_mem _ htIcc] at hd
    simpa [heq.eq_of_nhds] using hd.congr_of_eventuallyEq heq
  refine ⟨x, ⟨hx₀, hx⟩, ?_⟩
  intro y hy
  funext t
  obtain ⟨N, hN⟩ := exists_nat_gt |t - t₀|
  have hNpos : 0 < (N : ℝ) := (abs_nonneg _).trans_lt hN
  apply fundMatrix_linear_uniqueOn B hB t₀ N hNpos
    (x := y) (y := x) (fun s _ ↦ hy.2 s) (fun s _ ↦ hx s)
    (hy.1.trans hx₀.symm)
  rw [abs_lt] at hN
  constructor <;> linarith

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

/--
[fundMatrix_hasDerivAt_entry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma fundMatrix_hasDerivAt_entry {n : ℕ}
  {Φ : ℝ → Matrix (Fin n) (Fin n) ℝ} {N : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
  (hΦ : HasDerivAt Φ N t) (i j : Fin n) :
  HasDerivAt (fun s ↦ Φ s i j) (N i j) t :=
(hasDerivAt_pi.mp (hasDerivAt_pi.mp hΦ i)) j

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

/--
[fundMatrix_hasDerivAt_det](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma fundMatrix_hasDerivAt_det {n : ℕ}
  {Φ : ℝ → Matrix (Fin n) (Fin n) ℝ} {N : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
  (hΦ : HasDerivAt Φ N t) :
  HasDerivAt (fun s ↦ (Φ s).det) (fundMatrix_detDifferential (Φ t) N) t := by
  classical
  have hterm (σ : Equiv.Perm (Fin n)) : HasDerivAt
    (fun s ↦ ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, Φ s (σ i) i)
    (((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ∑ i, (∏ j ∈ Finset.univ.erase i, Φ t (σ j) j) * N (σ i) i) t := by
    apply HasDerivAt.const_mul
    convert HasDerivAt.fun_finsetProd (u := Finset.univ)
      (fun i _ ↦ fundMatrix_hasDerivAt_entry hΦ (σ i) i) using 1
  simpa only [Matrix.det_apply', fundMatrix_detDifferential] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ ↦ hterm σ)

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

/--
[fundMatrix_hasDerivAt_det_one_add_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma fundMatrix_hasDerivAt_det_one_add_smul {n : ℕ}
  (A : Matrix (Fin n) (Fin n) ℝ) :
  HasDerivAt (fun s : ℝ ↦ (1 + s • A).det) A.trace 0 := by
  let p : Polynomial ℝ :=
    (1 + (Polynomial.X : Polynomial ℝ) • A.map (Polynomial.C : ℝ → Polynomial ℝ)).det
  have hp : HasDerivAt (fun s ↦ p.eval s) A.trace 0 :=
    (p.hasDerivAt 0).congr_deriv (Matrix.derivative_det_one_add_X_smul A)
  apply hp.congr_of_eventuallyEq
  filter_upwards with s
  dsimp [p]
  simp [eval_det, ← Matrix.smul_eq_mul_diagonal]

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

/--
[fundMatrix_detDifferential_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma fundMatrix_detDifferential_mul {n : ℕ}
  (A M : Matrix (Fin n) (Fin n) ℝ) :
  fundMatrix_detDifferential M (A * M) = A.trace * M.det := by
  let ψ : ℝ → Matrix (Fin n) (Fin n) ℝ := fun s ↦ M + s • (A * M)
  have hψ : HasDerivAt ψ (A * M) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    change HasDerivAt (fun s : ℝ ↦ M i j + s * (A * M) i j) ((A * M) i j) 0
    convert ((hasDerivAt_id' (𝕜 := ℝ) 0).mul_const ((A * M) i j)).const_add (M i j) using 1
    ring
  have hleft : HasDerivAt (fun s ↦ (ψ s).det)
    (fundMatrix_detDifferential M (A * M)) 0 := by
    simpa [ψ] using fundMatrix_hasDerivAt_det hψ
  have hright : HasDerivAt (fun s ↦ (ψ s).det) (A.trace * M.det) 0 := by
    apply (fundMatrix_hasDerivAt_det_one_add_smul A).mul_const M.det |>.congr_of_eventuallyEq
    filter_upwards with s
    rw [show ψ s = (1 + s • A) * M by simp [ψ, add_mul], Matrix.det_mul]
  exact hleft.unique hright

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

/--
[det_of_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
lemma _root_.HasDerivAt.det_of_mul {n : ℕ}
  {Φ : ℝ → Matrix (Fin n) (Fin n) ℝ} {A : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
  (hΦ : HasDerivAt Φ (A * Φ t) t) :
  HasDerivAt (fun s ↦ (Φ s).det) (A.trace * (Φ t).det) t := by
  rw [← fundMatrix_detDifferential_mul A (Φ t)]
  exact fundMatrix_hasDerivAt_det hΦ

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

/--
[fundMatrix_hasDerivAt_mulVec_const](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma fundMatrix_hasDerivAt_mulVec_const {n : ℕ}
  {Φ : ℝ → Matrix (Fin n) (Fin n) ℝ} {N : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
  (hΦ : HasDerivAt Φ N t) (x : Fin n → ℝ) :
  HasDerivAt (fun s ↦ (Φ s).mulVec x) (N.mulVec x) t := by
  apply hasDerivAt_pi.mpr
  intro i
  simpa only [Matrix.mulVec_apply_eq_sum] using
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun j _ ↦ (fundMatrix_hasDerivAt_entry hΦ i j).mul_const (x j))

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

/--
[fundMatrix_liouville](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma fundMatrix_liouville {n : ℕ}
  (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ) (hA : Continuous A)
  (Φ : ℝ → Matrix (Fin n) (Fin n) ℝ)
  (hΦ : ∀ t, HasDerivAt Φ (A t * Φ t) t) (t : ℝ) :
  (Φ t).det = (Φ t₀).det * Real.exp (∫ s in t₀..t, (A s).trace) := by
  let I : ℝ → ℝ := fun u ↦ ∫ s in t₀..u, (A s).trace
  have htrace : Continuous (fun s ↦ (A s).trace) := hA.matrix_trace
  have hI (u : ℝ) : HasDerivAt I (A u).trace u := by
    exact intervalIntegral.integral_hasDerivAt_right
      (htrace.intervalIntegrable t₀ u)
      (htrace.stronglyMeasurableAtFilter volume (nhds u)) htrace.continuousAt
  let w : ℝ → ℝ := fun u ↦ (Φ u).det * Real.exp (-I u)
  have hw (u : ℝ) : HasDerivAt w 0 u := by
    have hd := HasDerivAt.det_of_mul (hΦ u)
    have he := (hI u).neg.exp
    convert hd.mul he using 1
    ring
  have hw_const : w t = w t₀ :=
    is_const_of_deriv_eq_zero (fun u ↦ (hw u).differentiableAt)
      (fun u ↦ (hw u).deriv) t t₀
  have hw_eq : (Φ t).det * Real.exp (-I t) = (Φ t₀).det := by
    simpa [w, I] using hw_const
  calc
    (Φ t).det = ((Φ t).det * Real.exp (-I t)) * Real.exp (I t) := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ = (Φ t₀).det * Real.exp (I t) := by rw [hw_eq]
    _ = (Φ t₀).det * Real.exp (∫ s in t₀..t, (A s).trace) := rfl

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

/--
[fundamental_matrix_linear_system](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
lemma fundamental_matrix_linear_system
  {n : ℕ}
  {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
  {t₀ : ℝ}
-- given
  (hA : Continuous A) :
-- imply
  ∃ Φ : ℝ → Matrix (Fin n) (Fin n) ℝ, Φ t₀ = 1 ∧
    (∀ t, HasDerivAt Φ (A t * Φ t) t) ∧
    (∀ t, IsUnit (Φ t).det) ∧
    ∀ x₀ : Fin n → ℝ, ∃ x : ℝ → (Fin n → ℝ),
    x t₀ = x₀ ∧ (∀ t, HasDerivAt x ((A t).mulVec (x t)) t) ∧
    (∀ t, x t = (Φ t).mulVec x₀) ∧
    ∀ y : ℝ → (Fin n → ℝ), y t₀ = x₀ →
    (∀ t, HasDerivAt y ((A t).mulVec (y t)) t) → y = x := by
-- proof
  let B : ℝ → (Fin n → Fin n → ℝ) →L[ℝ] Fin n → Fin n → ℝ :=
    fun t ↦ fundMatrix_matrixMulCLM (A t)
  have hB : Continuous B := fundMatrix_matrixMulCLM.continuous.comp hA
  obtain ⟨φ, hφ0, hφ⟩ :=
    (ODE.existsUnique_hasDerivAt_eq_continuousLinearMap B t₀
      (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℝ)) hB).exists
  let Φ : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t ↦ Matrix.of (φ t)
  have hΦ0 : Φ t₀ = 1 := by simp [Φ, hφ0]
  have hΦ' (t : ℝ) : HasDerivAt Φ (A t * Φ t) t := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    simpa [Φ, B] using (hasDerivAt_pi.mp (hasDerivAt_pi.mp (hφ t) i) j)
  refine ⟨Φ, hΦ0, hΦ', ?_, ?_⟩
  · intro t
    apply isUnit_iff_ne_zero.mpr
    rw [fundMatrix_liouville A t₀ hA Φ hΦ' t, hΦ0]
    simp
  · intro x₀
    let x : ℝ → Fin n → ℝ := fun t ↦ (Φ t).mulVec x₀
    have hx0 : x t₀ = x₀ := by simp [x, hΦ0]
    have hx (t : ℝ) : HasDerivAt x ((A t).mulVec (x t)) t := by
      simpa only [x, Matrix.mulVec_mulVec] using
        fundMatrix_hasDerivAt_mulVec_const (hΦ' t) x₀
    let C : ℝ → (Fin n → ℝ) →L[ℝ] Fin n → ℝ :=
      fun t ↦ fundMatrix_mulVecCLM (A t)
    have hC : Continuous C := fundMatrix_mulVecCLM.continuous.comp hA
    obtain ⟨z, hz, hunique⟩ :=
      ODE.existsUnique_hasDerivAt_eq_continuousLinearMap C t₀ x₀ hC
    have hxz : x = z := hunique x ⟨hx0, fun t ↦ by simpa [C] using hx t⟩
    refine ⟨x, hx0, hx, fun _ ↦ rfl, ?_⟩
    intro y hy0 hy
    exact (hunique y ⟨hy0, fun t ↦ by simpa [C] using hy t⟩).trans hxz.symm

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

/--
[fundamental_matrix_liouville_det](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
lemma fundamental_matrix_liouville_det
  {n : ℕ}
  {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
  {t₀ : ℝ}
  {Φ : ℝ → Matrix (Fin n) (Fin n) ℝ}
-- given
  (hA : Continuous A)
  (hΦ0 : Φ t₀ = 1)
  (hΦ : ∀ t, HasDerivAt Φ (A t * Φ t) t) :
-- imply
  ∀ t, (Φ t).det = (Φ t₀).det * Real.exp (∫ s in t₀..t, (A s).trace) := by
-- proof
  exact fundMatrix_liouville A t₀ hA Φ hΦ

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

/--
[_root_.ODE.existsUnique_hasDerivAt_eq_continuousLinearMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma ODE_existsUnique_hasDerivAt_eq_continuousLinearMap_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {B : ℝ → E →L[ℝ] E}
  {t₀ : ℝ}
  {x₀ : E}
-- given
  (hB : Continuous B) :
-- imply
  ∃! x : ℝ → E, x t₀ = x₀ ∧ ∀ t, HasDerivAt x (B t (x t)) t := by
-- proof
  apply ODE.existsUnique_hasDerivAt_eq_continuousLinearMap B t₀ x₀ hB

/--
[_root_.HasDerivAt.det_of_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean)
-/
@[path]
private lemma HasDerivAt_det_of_mul_eq
  {n : ℕ}
  {Φ : ℝ → Matrix (Fin n) (Fin n) ℝ}
  {A : Matrix (Fin n) (Fin n) ℝ}
  {t : ℝ}
-- given
  (hΦ : HasDerivAt Φ (A * Φ t) t) :
-- imply
  HasDerivAt (fun s ↦ (Φ s).det) (A.trace * (Φ t).det) t := by
-- proof
  apply HasDerivAt.det_of_mul hΦ


-- created on 2026-10-20
-- updated on 2026-10-23
