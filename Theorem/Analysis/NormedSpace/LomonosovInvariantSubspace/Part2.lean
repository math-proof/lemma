/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Def.Analysis.NormedSpace.LomonosovInvariantSubspace


namespace FunctionalAnalysis.LomonosovInvariantSubspaceWanted

/-- Membership in the orbit submodule. -/
theorem lomo_mem_orb
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : E →L[ℂ] E) (y z : E) :
    z ∈ lomoOrb K y ↔ ∃ A : E →L[ℂ] E, A ∈ lomoCentralizer K ∧ A y = z := by
  simp [lomoOrb, Submodule.mem_map, Subalgebra.mem_toSubmodule,
    ContinuousLinearMap.apply_apply]

/-- `T` lies in the centralizer of `K`. -/
theorem lomo_T_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K T : E →L[ℂ] E) (hComm : T.comp K = K.comp T) :
    T ∈ lomoCentralizer K := by
  change T ∈ Subalgebra.centralizer ℂ {K}
  rw [Subalgebra.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  rw [ContinuousLinearMap.mul_def]
  exact hComm.symm

/-- Case B1: a proper nonzero closed orbit is the wanted subspace. -/
theorem lomo_exists_of_orbit_ne_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E) (T : E →L[ℂ] E) (hComm : T.comp K = K.comp T)
    (y : E) (hy : y ≠ 0) (hne : lomoOrbit K y ≠ ⊤) :
    ∃ (M : Submodule ℂ E), M ≠ ⊥ ∧ M ≠ ⊤ ∧ IsClosed (M : Set E) ∧ ∀ x ∈ M, T x ∈ M := by
  have hTmem : T ∈ lomoCentralizer K := lomo_T_mem K T hComm
  have hmaps : Set.MapsTo T (lomoOrb K y : Set E) (lomoOrb K y : Set E) := by
    intro z hz
    have hz' : z ∈ lomoOrb K y := hz
    rw [lomo_mem_orb] at hz'
    obtain ⟨A, hA, rfl⟩ := hz'
    change T (A y) ∈ lomoOrb K y
    rw [lomo_mem_orb]
    refine ⟨T * A, mul_mem hTmem hA, ?_⟩
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  refine ⟨lomoOrbit K y, ?_, hne, Submodule.isClosed_topologicalClosure (lomoOrb K y), ?_⟩
  · rw [Submodule.ne_bot_iff]
    refine ⟨y, ?_, hy⟩
    apply Submodule.le_topologicalClosure
    rw [lomo_mem_orb]
    exact ⟨1, Subalgebra.one_mem _, by simp⟩
  · intro x hx
    have hx' : x ∈ closure (lomoOrb K y : Set E) := by
      have hmem : x ∈ ((lomoOrb K y).topologicalClosure : Set E) := hx
      rwa [Submodule.topologicalClosure_coe] at hmem
    have hTx : T x ∈ closure (lomoOrb K y : Set E) :=
      map_mem_closure T.continuous hx' hmaps
    have hmem2 : T x ∈ ((lomoOrb K y).topologicalClosure : Set E) := by
      rwa [Submodule.topologicalClosure_coe]
    exact hmem2

/-- Setup for Hilden's iteration: a ball mapped by `K` into a compact set away from 0. -/
theorem lomo_exists_ball_setup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E) (hK_compact : IsCompactOperator K) (hK_ne : K ≠ 0) :
    ∃ (x0 : E) (r : ℝ), 0 < r ∧ ∃ (S : Set E), IsCompact S ∧ 0 ∉ S ∧
      (∀ x ∈ Metric.closedBall x0 r, K x ∈ S) ∧
      (∀ x ∈ Metric.closedBall x0 r, r ≤ ‖x‖) := by
  obtain ⟨x0, hx0⟩ : ∃ x0, K x0 ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hK_ne
    ext x
    simpa using h x
  have ha : (0 : ℝ) < ‖K x0‖ := norm_pos_iff.mpr hx0
  have hk : (0 : ℝ) < ‖K‖ := norm_pos_iff.mpr hK_ne
  have hKne : (‖K‖ : ℝ) ≠ 0 := ne_of_gt hk
  set r : ℝ := ‖K x0‖ / (2 * ‖K‖) with hr_def
  have h2k : (0 : ℝ) < 2 * ‖K‖ := mul_pos (by norm_num) hk
  have hnpos : (0 : ℝ) < r := by
    rw [hr_def]
    exact div_pos ha h2k
  have hKr : ‖K‖ * r = ‖K x0‖ / 2 := by
    rw [hr_def]
    field_simp
  have hmem : ∀ x ∈ Metric.closedBall x0 r, ‖x - x0‖ ≤ r := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    exact hx
  have hKx : ∀ x ∈ Metric.closedBall x0 r, ‖K x0‖ / 2 ≤ ‖K x‖ := by
    intro x hx
    have hle : ‖K (x - x0)‖ ≤ ‖K‖ * r :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (hmem x hx) (le_of_lt hk))
    have heq : K (x - x0) = K x - K x0 := map_sub K x x0
    have htri : ‖K x0‖ - ‖K x‖ ≤ ‖K x - K x0‖ := by
      have h := norm_sub_norm_le (K x0) (K x)
      rwa [norm_sub_rev] at h
    rw [← heq] at htri
    linarith [hle, hKr]
  have hx0ge : 2 * r ≤ ‖x0‖ := by
    by_contra hlt
    have hlt' : ‖x0‖ < 2 * r := lt_of_not_ge hlt
    have h1 : ‖K‖ * ‖x0‖ < ‖K‖ * (2 * r) := mul_lt_mul_of_pos_left hlt' hk
    have h2 : ‖K‖ * (2 * r) = ‖K x0‖ := by linear_combination 2 * hKr
    have h3 : ‖K x0‖ ≤ ‖K‖ * ‖x0‖ := ContinuousLinearMap.le_opNorm _ _
    linarith
  have hxr : ∀ x ∈ Metric.closedBall x0 r, r ≤ ‖x‖ := by
    intro x hx
    have h1 : ‖x0‖ - ‖x‖ ≤ ‖x - x0‖ := by
      have h := norm_sub_norm_le x0 x
      rwa [norm_sub_rev] at h
    linarith [hmem x hx, hx0ge]
  obtain ⟨K', hK'comp, hsub⟩ :=
    hK_compact.image_closedBall_subset_compact (‖x0‖ + r)
  have hxball : ∀ x ∈ Metric.closedBall x0 r,
      x ∈ Metric.closedBall (0 : E) (‖x0‖ + r) := by
    intro x hx
    have htri : ‖x‖ ≤ ‖x0‖ + ‖x - x0‖ := by
      have h := norm_add_le x0 (x - x0)
      rwa [add_sub_cancel] at h
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    linarith [htri, hmem x hx]
  refine ⟨x0, r, hnpos, K' ∩ {y | ‖K x0‖ / 2 ≤ ‖y‖}, ?_, ?_, ?_, hxr⟩
  · exact hK'comp.inter_right (isClosed_le continuous_const continuous_norm)
  · intro h0
    obtain ⟨-, h⟩ := h0
    simp only [Set.mem_ofPred_eq, norm_zero] at h
    linarith
  · intro x hx
    constructor
    · apply hsub
      exact ⟨x, hxball x hx, rfl⟩
    · exact hKx x hx

/-- Finite subcover of a compact set by centralizer preimages of a ball. -/
theorem lomo_exists_finite_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E)
    (htrans : ∀ y : E, y ≠ 0 → lomoOrbit K y = ⊤)
    (S : Set E) (hS : IsCompact S) (h0S : (0 : E) ∉ S)
    (x0 : E) (r : ℝ) (hr : 0 < r) :
    ∃ F : Finset (lomoCentralizer K),
      ∀ y ∈ S, ∃ A ∈ F, dist ((A : E →L[ℂ] E) y) x0 < r := by
  have hcover : S ⊆ ⋃ A : lomoCentralizer K, (A : E →L[ℂ] E) ⁻¹' Metric.ball x0 r := by
    intro y hy
    have hyne : y ≠ 0 := fun h => h0S (h ▸ hy)
    have htop : lomoOrbit K y = ⊤ := htrans y hyne
    have hdense : Dense (lomoOrb K y : Set E) := by
      rw [Submodule.dense_iff_topologicalClosure_eq_top]
      exact htop
    obtain ⟨z, hz, hdist⟩ := hdense.exists_dist_lt x0 hr
    have hz' : z ∈ lomoOrb K y := hz
    rw [lomo_mem_orb] at hz'
    obtain ⟨A, hA, rfl⟩ := hz'
    have hmem : y ∈ ((⟨A, hA⟩ : lomoCentralizer K) : E →L[ℂ] E) ⁻¹' Metric.ball x0 r := by
      change A y ∈ Metric.ball x0 r
      rw [Metric.mem_ball, dist_comm]
      exact hdist
    exact Set.mem_iUnion.mpr ⟨⟨A, hA⟩, hmem⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun A : lomoCentralizer K => (A : E →L[ℂ] E) ⁻¹' Metric.ball x0 r)
    (fun A => IsOpen.preimage (A : E →L[ℂ] E).continuous Metric.isOpen_ball) hcover
  refine ⟨t, ?_⟩
  intro y hy
  obtain ⟨A, hAt, hAy⟩ := Set.mem_iUnion₂.mp (ht hy)
  have hmem : (A : E →L[ℂ] E) y ∈ Metric.ball x0 r := hAy
  refine ⟨A, hAt, ?_⟩
  rw [Metric.mem_ball] at hmem
  exact hmem

/-- Hilden's iteration: centralizer operators tracking `K^m x0` in the ball. -/
theorem lomo_iterate_mem_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E)
    (x0 : E) (r : ℝ) (hr : 0 ≤ r) (c : ℝ) (hc : 0 ≤ c)
    (F : Finset (lomoCentralizer K))
    (hFnorm : ∀ A ∈ F, ‖(A : E →L[ℂ] E)‖ ≤ c)
    (hcov : ∀ x ∈ Metric.closedBall x0 r,
      ∃ A ∈ F, ((A : E →L[ℂ] E) (K x)) ∈ Metric.closedBall x0 r) :
    ∀ m : ℕ, ∃ P : E →L[ℂ] E, P ∈ lomoCentralizer K ∧ ‖P‖ ≤ c ^ m ∧
      P ((K ^ m) x0) ∈ Metric.closedBall x0 r := by
  intro m
  induction m with
  | zero =>
    refine ⟨1, Subalgebra.one_mem _, ?_, ?_⟩
    · rw [pow_zero, ContinuousLinearMap.one_def]
      exact ContinuousLinearMap.norm_id_le
    · have hmem : x0 ∈ Metric.closedBall x0 r :=
        Metric.mem_closedBall.mpr (by simpa using hr)
      have h1 : (1 : E →L[ℂ] E) ((K ^ 0) x0) = x0 := rfl
      rwa [h1]
  | succ m ih =>
    obtain ⟨P, hP, hPnorm, hPmem⟩ := ih
    obtain ⟨A, hAF, hAmem⟩ := hcov _ hPmem
    have hP' : P ∈ Subalgebra.centralizer ℂ {K} := hP
    rw [Subalgebra.mem_centralizer_iff] at hP'
    have hPc : K * P = P * K := hP' K (Set.mem_singleton K)
    have hKP : ∀ w : E, K (P w) = P (K w) := by
      intro w
      have h := congrArg (fun Q : E →L[ℂ] E => Q w) hPc
      simpa [ContinuousLinearMap.mul_def] using h
    have heq : ((A : E →L[ℂ] E) * P) ((K ^ (m + 1)) x0)
        = (A : E →L[ℂ] E) (K (P ((K ^ m) x0))) := by
      rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hKP]
    have h3 : c * c ^ m = c ^ (m + 1) := (pow_succ' c m).symm
    refine ⟨(A : E →L[ℂ] E) * P, mul_mem A.property hP, ?_, ?_⟩
    · rw [← h3]
      exact (norm_mul_le _ _).trans
        (mul_le_mul (hFnorm A hAF) hPnorm (norm_nonneg _) hc)
    · rw [heq]
      exact hAmem

/-- Case B2: transitivity of the centralizer action is impossible. -/
theorem lomo_false_of_transitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E) (hK_compact : IsCompactOperator K) (hK_ne : K ≠ 0)
    (hno : ∀ μ : ℂ, ¬ Module.End.HasEigenvalue (↑K : Module.End ℂ E) μ)
    (htrans : ∀ y : E, y ≠ 0 → lomoOrbit K y = ⊤) :
    False := by
  have hspec : spectralRadius ℂ K = 0 :=
    lomo_spectralRadius_eq_zero K hK_compact (fun μ _ => hno μ)
  obtain ⟨x0, r, hr, S, hScomp, h0S, hKS, hxr⟩ :=
    lomo_exists_ball_setup K hK_compact hK_ne
  obtain ⟨F, hF⟩ := lomo_exists_finite_cover K htrans S hScomp h0S x0 r hr
  set c : ℝ := 1 + ∑ A ∈ F, ‖(A : E →L[ℂ] E)‖ with hc_def
  have hc : (0 : ℝ) ≤ c := by
    rw [hc_def]
    have hnn : (0 : ℝ) ≤ ∑ A ∈ F, ‖(A : E →L[ℂ] E)‖ :=
      Finset.sum_nonneg (fun A _ => norm_nonneg _)
    linarith
  have hFnorm : ∀ A ∈ F, ‖(A : E →L[ℂ] E)‖ ≤ c := by
    intro A hA
    rw [hc_def]
    exact (Finset.single_le_sum (fun B _ => norm_nonneg _) hA).trans
      (le_add_of_nonneg_left zero_le_one)
  have hcov : ∀ x ∈ Metric.closedBall x0 r,
      ∃ A ∈ F, ((A : E →L[ℂ] E) (K x)) ∈ Metric.closedBall x0 r := by
    intro x hx
    obtain ⟨A, hAF, hdist⟩ := hF (K x) (hKS x hx)
    exact ⟨A, hAF, Metric.ball_subset_closedBall (Metric.mem_ball.mpr hdist)⟩
  have hlim2 : Filter.Tendsto (fun m : ℕ => c ^ m * ‖K ^ m‖ * ‖x0‖) Filter.atTop
      (nhds 0) := by
    simpa using (lomo_tendsto_const_pow_mul_norm_pow K hspec c hc).mul_const ‖x0‖
  have hev : ∀ᶠ m : ℕ in Filter.atTop, c ^ m * ‖K ^ m‖ * ‖x0‖ < r :=
    hlim2.eventually (Iio_mem_nhds hr)
  have hlow : ∀ m : ℕ, r ≤ c ^ m * ‖K ^ m‖ * ‖x0‖ := by
    intro m
    obtain ⟨P, -, hPnorm, hPmem⟩ :=
      lomo_iterate_mem_closedBall K x0 r (le_of_lt hr) c hc F hFnorm hcov m
    have h1 : r ≤ ‖P ((K ^ m) x0)‖ := hxr _ hPmem
    have h2 : ‖P ((K ^ m) x0)‖ ≤ ‖P‖ * (‖K ^ m‖ * ‖x0‖) :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
    have h3 : ‖P‖ * (‖K ^ m‖ * ‖x0‖) ≤ c ^ m * ‖K ^ m‖ * ‖x0‖ := by
      have h31 : ‖P‖ * ‖K ^ m‖ ≤ c ^ m * ‖K ^ m‖ :=
        mul_le_mul_of_nonneg_right hPnorm (norm_nonneg _)
      calc ‖P‖ * (‖K ^ m‖ * ‖x0‖) = (‖P‖ * ‖K ^ m‖) * ‖x0‖ := by ring
        _ ≤ (c ^ m * ‖K ^ m‖) * ‖x0‖ := mul_le_mul_of_nonneg_right h31 (norm_nonneg _)
    linarith [h1, h2, h3]
  obtain ⟨m, hm⟩ := (hev.and (Filter.Eventually.of_forall hlow)).exists
  exact absurd hm.2 (not_le_of_gt hm.1)

/--
In an infinite-dimensional complex Banach space `E`, if `K ≠ 0` is compact and `T : E →L[ℂ] E`
commutes with `K`, then `T` has a nontrivial proper closed `ℂ`-invariant subspace `M` with `M ≠
⊥`, `M ≠ ⊤`, `IsClosed M`, `T '' M ⊆ M`. Source: V. Lomonosov, Functional Anal. Appl. 7 (1973)
and J. Hilden elementary proof, Bull. Amer. Math. Soc.; Aronszajn-Smith 1954 precursor;
Radjavi-Rosenthal invariant subspace book, 1973; Lean states complex Banach infinite-dimensional
case `K≠0` compact commuting with `T` yields nontrivial closed invariant subspace.

Proves `Wanted` entry `lomonosov_invariantSubspace`.
-/
theorem lomonosov_invariantSubspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (hInf : ¬ FiniteDimensional ℂ E)
    (K : E →L[ℂ] E) (hK_compact : IsCompactOperator K) (hK_ne : K ≠ 0)
    (T : E →L[ℂ] E) (hComm : T.comp K = K.comp T) :
    ∃ (M : Submodule ℂ E), M ≠ ⊥ ∧ M ≠ ⊤ ∧ IsClosed (M : Set E) ∧ ∀ x ∈ M, T x ∈ M := by
  by_cases hA : ∃ μ, Module.End.HasEigenvalue (↑K : Module.End ℂ E) μ
  · obtain ⟨μ, hμ⟩ := hA
    exact lomo_exists_of_hasEigenvalue hInf K hK_compact hK_ne T hComm μ hμ
  · have hno : ∀ μ : ℂ, ¬ Module.End.HasEigenvalue (↑K : Module.End ℂ E) μ :=
      fun μ h => hA ⟨μ, h⟩
    by_cases hB : ∃ y : E, y ≠ 0 ∧ lomoOrbit K y ≠ ⊤
    · obtain ⟨y, hy, hne⟩ := hB
      exact lomo_exists_of_orbit_ne_top K T hComm y hy hne
    · have htrans : ∀ y : E, y ≠ 0 → lomoOrbit K y = ⊤ := by
        intro y hy
        by_contra hne
        exact hB ⟨y, hy, hne⟩
      exact False.elim (lomo_false_of_transitive K hK_compact hK_ne hno htrans)

end FunctionalAnalysis.LomonosovInvariantSubspaceWanted
