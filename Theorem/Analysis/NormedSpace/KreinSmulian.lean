/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Data.List.GetD
import Mathlib.Basic.Real.Sign
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Def.Analysis.NormedSpace.KreinSmulian


namespace FunctionalAnalysis.BanachSpaceWanted

open Set Metric

open scoped ComplexConjugate ZeroAtInfty

/-- Real polar of a ball: control of real parts on a ball bounds the dual norm. -/
lemma ks_norm_le_of_rpol {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {ρ : ℝ} (hρ : 0 < ρ) {φ : WeakDual 𝕜 E}
    (h : ∀ x : E, ‖x‖ ≤ ρ → RCLike.re (φ x) ≤ 1) :
    ‖WeakDual.toStrongDual φ‖ ≤ ρ⁻¹ := by
  have hnorm : ∀ x : E, x ∈ closedBall (0 : E) ρ → ‖φ x‖ ≤ 1 := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx
    by_cases hzx : φ x = 0
    · rw [hzx, norm_zero]
      exact zero_le_one
    · have hnpos : 0 < ‖φ x‖ := norm_pos_iff.mpr hzx
      have hne : ((‖φ x‖ : ℝ) : 𝕜) ≠ 0 :=
        RCLike.ofReal_ne_zero.mpr (ne_of_gt hnpos)
      have hrot : φ ((conj (φ x) / ((‖φ x‖ : ℝ) : 𝕜)) • x) = ((‖φ x‖ : ℝ) : 𝕜) := by
        have e1 : φ ((conj (φ x) / ((‖φ x‖ : ℝ) : 𝕜)) • x)
            = (conj (φ x) / ((‖φ x‖ : ℝ) : 𝕜)) * φ x := by
          rw [map_smul, smul_eq_mul]
        rw [e1, div_mul_eq_mul_div, RCLike.conj_mul, sq, mul_div_cancel_left₀ _ hne]
      have hmem : (conj (φ x) / ((‖φ x‖ : ℝ) : 𝕜)) • x ∈ closedBall (0 : E) ρ := by
        rw [mem_closedBall_zero_iff, norm_smul]
        have hcnorm : ‖conj (φ x) / ((‖φ x‖ : ℝ) : 𝕜)‖ = 1 := by
          rw [norm_div, RCLike.norm_conj, RCLike.norm_ofReal, abs_of_pos hnpos,
            div_self (ne_of_gt hnpos)]
        rw [hcnorm, one_mul]
        exact hx
      have hre := h _ (mem_closedBall_zero_iff.mp hmem)
      rw [hrot, RCLike.ofReal_re] at hre
      exact hre
  have hmem : WeakDual.toStrongDual φ ∈ StrongDual.polar 𝕜 (closedBall (0 : E) ρ) := by
    rw [StrongDual.mem_polar_iff]
    intro z hz
    rw [WeakDual.toStrongDual_apply]
    exact hnorm z hz
  rw [NormedSpace.polar_closedBall hρ] at hmem
  exact mem_closedBall_zero_iff.mp hmem

/-- Sublevel sets of real parts of evaluations are weak-* closed. -/
lemma ks_isClosed_re_le {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (x : E) (c : ℝ) :
    IsClosed {φ : WeakDual 𝕜 E | RCLike.re (φ x) ≤ c} :=
  isClosed_le (RCLike.continuous_re.comp (WeakDual.eval_continuous x)) continuous_const

/-- Superlevel sets of real parts of evaluations are weak-* closed. -/
lemma ks_isClosed_le_re {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (x : E) (c : ℝ) :
    IsClosed {φ : WeakDual 𝕜 E | c ≤ RCLike.re (φ x)} :=
  isClosed_le continuous_const (RCLike.continuous_re.comp (WeakDual.eval_continuous x))

/-- Real polars are weak-* closed. -/
lemma ks_isClosed_rpol {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (F : Set E) : IsClosed (ks_rpol (𝕜 := 𝕜) F) := by
  have heq : ks_rpol (𝕜 := 𝕜) F
      = ⋂ x ∈ F, {φ : WeakDual 𝕜 E | RCLike.re (φ x) ≤ 1} := by
    ext φ
    simp [ks_rpol]
  rw [heq]
  exact isClosed_biInter fun x _ => ks_isClosed_re_le x 1

/-- Dual norm balls are weak-* closed. -/
lemma ks_isClosed_ball {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (r : ℝ) :
    IsClosed (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r) :=
  WeakDual.isClosed_closedBall 0 r

/-- Dual norm balls are weak-* compact. -/
lemma ks_isCompact_ball {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (r : ℝ) :
    IsCompact (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r) :=
  WeakDual.isCompact_closedBall 0 r

/-- A norm gap: if `0 ∉ K` and `K ∩ B 1` is closed, dual norms on `K` stay above
some positive `δ ≤ 1`. -/
lemma ks_norm_gap {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {K : Set (WeakDual 𝕜 E)} (h0 : (0 : WeakDual 𝕜 E) ∉ K)
    (hcl : IsClosed (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ φ : WeakDual 𝕜 E, φ ∈ K → δ < ‖WeakDual.toStrongDual φ‖ := by
  have hUopen :
      IsOpen (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)ᶜ :=
    hcl.isOpen_compl
  have h0U : (0 : WeakDual 𝕜 E)
      ∈ (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)ᶜ :=
    fun h => h0 h.1
  have hcont : Continuous fun x' : StrongDual 𝕜 E => StrongDual.toWeakDual x' :=
    NormedSpace.Dual.toWeakDual_continuous
  have hVopen : IsOpen ((fun x' : StrongDual 𝕜 E => StrongDual.toWeakDual x') ⁻¹'
      (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)ᶜ) :=
    hUopen.preimage hcont
  have h0V : (0 : StrongDual 𝕜 E) ∈ (fun x' : StrongDual 𝕜 E => StrongDual.toWeakDual x') ⁻¹'
      (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)ᶜ := by
    change StrongDual.toWeakDual 0 ∈
      (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)ᶜ
    rw [map_zero]
    exact h0U
  rw [Metric.isOpen_iff] at hVopen
  obtain ⟨ε, hε, hball⟩ := hVopen 0 h0V
  refine ⟨min (ε / 2) 1, lt_min (by linarith) zero_lt_one, min_le_right _ _, fun φ hφ => ?_⟩
  by_contra hcon
  have hle : ‖WeakDual.toStrongDual φ‖ ≤ min (ε / 2) 1 := le_of_not_gt hcon
  have hB : φ ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1 := by
    change WeakDual.toStrongDual φ ∈ closedBall (0 : StrongDual 𝕜 E) 1
    rw [mem_closedBall_zero_iff]
    exact le_trans hle (min_le_right _ _)
  have hball' : WeakDual.toStrongDual φ ∈ ball (0 : StrongDual 𝕜 E) ε := by
    rw [mem_ball_zero_iff]
    exact lt_of_le_of_lt hle (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε))
  have hmem : StrongDual.toWeakDual (WeakDual.toStrongDual φ) ∈
      (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)ᶜ :=
    hball hball'
  rw [WeakDual.toWeakDual_toStrongDual] at hmem
  exact hmem ⟨hφ, hB⟩

/-- One step of the Banach–Dieudonné construction: enlarge `G` by finitely many
small vectors so the next ball intersection becomes empty. -/
lemma ks_step {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {K : Set (WeakDual 𝕜 E)}
    (hK : ∀ r : ℝ, 0 < r →
      IsClosed (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r))
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 1 ≤ n) {G : Finset E}
    (hempty : K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * (n : ℝ))
      ∩ ks_rpol (𝕜 := 𝕜) ↑G = ∅) :
    ∃ F : Finset E, (∀ x ∈ F, ‖x‖ ≤ (δ * (n : ℝ))⁻¹) ∧
      K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((n : ℝ) + 1))
        ∩ ks_rpol (𝕜 := 𝕜) (↑G ∪ ↑F) = ∅ := by
  classical
  have hn0 : 0 < n := by omega
  have hδn : 0 < δ * (n : ℝ) := mul_pos hδ (Nat.cast_pos.mpr hn0)
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hRpos : 0 < δ * ((n : ℝ) + 1) := mul_pos hδ (by linarith)
  have hQclosed : IsClosed (K ∩ WeakDual.toStrongDual ⁻¹'
      closedBall (0 : StrongDual 𝕜 E) (δ * ((n : ℝ) + 1)) ∩ ks_rpol (𝕜 := 𝕜) ↑G) :=
    (hK _ hRpos).inter (ks_isClosed_rpol _)
  have hQsub : (K ∩ WeakDual.toStrongDual ⁻¹'
      closedBall (0 : StrongDual 𝕜 E) (δ * ((n : ℝ) + 1)) ∩ ks_rpol (𝕜 := 𝕜) ↑G)
      ⊆ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((n : ℝ) + 1)) :=
    fun φ h => h.1.2
  have hQcompact : IsCompact (K ∩ WeakDual.toStrongDual ⁻¹'
      closedBall (0 : StrongDual 𝕜 E) (δ * ((n : ℝ) + 1)) ∩ ks_rpol (𝕜 := 𝕜) ↑G) :=
    (ks_isCompact_ball _).of_isClosed_subset hQclosed hQsub
  have hdisj : Disjoint (K ∩ WeakDual.toStrongDual ⁻¹'
        closedBall (0 : StrongDual 𝕜 E) (δ * ((n : ℝ) + 1)) ∩ ks_rpol (𝕜 := 𝕜) ↑G)
      (⋂ v : ↥(closedBall (0 : E) (δ * (n : ℝ))⁻¹),
        {φ : WeakDual 𝕜 E | RCLike.re (φ v.val) ≤ 1}) := by
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    intro φ hφ
    rw [Set.mem_inter_iff] at hφ
    obtain ⟨⟨⟨hKφ, hBφ⟩, hrpol⟩, hmem⟩ := hφ
    have hball : ∀ x : E, ‖x‖ ≤ (δ * (n : ℝ))⁻¹ → RCLike.re (φ x) ≤ 1 := by
      intro x hx
      exact (Set.mem_iInter.mp hmem) ⟨x, mem_closedBall_zero_iff.mpr hx⟩
    have hnorm := ks_norm_le_of_rpol (inv_pos.mpr hδn) hball
    rw [inv_inv] at hnorm
    have hmem2 : φ ∈ K ∩ WeakDual.toStrongDual ⁻¹'
        closedBall (0 : StrongDual 𝕜 E) (δ * (n : ℝ)) ∩ ks_rpol (𝕜 := 𝕜) ↑G := by
      refine ⟨⟨hKφ, ?_⟩, hrpol⟩
      change WeakDual.toStrongDual φ ∈ closedBall (0 : StrongDual 𝕜 E) (δ * (n : ℝ))
      rw [mem_closedBall_zero_iff]
      exact hnorm
    rw [hempty] at hmem2
    exact notMem_empty φ hmem2
  obtain ⟨u, hu⟩ := hQcompact.elim_finite_subfamily_closed
    (fun v : ↥(closedBall (0 : E) (δ * (n : ℝ))⁻¹) =>
      {φ : WeakDual 𝕜 E | RCLike.re (φ v.val) ≤ 1})
    (fun v => ks_isClosed_re_le v.val 1) hdisj
  refine ⟨u.image Subtype.val, fun x hx => ?_, ?_⟩
  · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact mem_closedBall_zero_iff.mp v.property
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro φ ⟨⟨hKφ, hBφ⟩, hrpol⟩
    have hrpol' : ∀ x ∈ (↑G ∪ ↑(u.image Subtype.val) : Set E), RCLike.re (φ x) ≤ 1 :=
      hrpol
    have hQu : φ ∈ K ∩ WeakDual.toStrongDual ⁻¹'
        closedBall (0 : StrongDual 𝕜 E) (δ * ((n : ℝ) + 1)) ∩ ks_rpol (𝕜 := 𝕜) ↑G := by
      refine ⟨⟨hKφ, hBφ⟩, fun x hx => hrpol' x (Set.mem_union_left _ hx)⟩
    have hI : φ ∈ ⋂ v ∈ u,
        {φ' : WeakDual 𝕜 E | RCLike.re (φ' v.val) ≤ 1} := by
      simp only [Set.mem_iInter]
      intro v hv
      have hFv : (v.val : E) ∈ u.image Subtype.val :=
        Finset.mem_image.mpr ⟨v, Finset.mem_coe.mp hv, rfl⟩
      exact hrpol' _ (Set.mem_union_right _ (Finset.mem_coe.mpr hFv))
    exact Set.disjoint_left.mp hu hQu hI

/-- The null family: countably many small vectors detecting every `φ ∈ K`. -/
lemma ks_null_family {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {K : Set (WeakDual 𝕜 E)}
    (hK : ∀ r : ℝ, 0 < r →
      IsClosed (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r))
    {δ : ℝ} (hδ : 0 < δ)
    (hKδ : K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) δ = ∅) :
    ∃ x : ℕ × ℕ → E, Filter.Tendsto x Filter.cofinite (nhds 0) ∧
      (∀ p, ‖x p‖ ≤ δ⁻¹) ∧
      (∀ φ : WeakDual 𝕜 E, φ ∈ K → ∃ p, 1 < RCLike.re (φ (x p))) := by
  classical
  have key : ∀ m : ℕ, ∀ G : Finset E,
      K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((m : ℝ) + 1))
        ∩ ks_rpol (𝕜 := 𝕜) ↑G = ∅ →
      ∃ F : Finset E, (∀ x ∈ F, ‖x‖ ≤ (δ * ((m : ℝ) + 1))⁻¹) ∧
        K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((m : ℝ) + 2))
          ∩ ks_rpol (𝕜 := 𝕜) (↑G ∪ ↑F) = ∅ := by
    intro m G h
    have e1 : ((m : ℝ) + 1) = ((((m + 1 : ℕ)) : ℝ)) := by
      rw [Nat.cast_add_one]
    have e2 : ((m : ℝ) + 2) = (((((m + 1 : ℕ)) : ℝ)) + 1) := by
      rw [Nat.cast_add_one]; ring
    rw [e1] at h
    obtain ⟨F, hFb, hFe⟩ := ks_step hK hδ (n := m + 1) (by omega) (G := G) h
    rw [← e1] at hFb
    rw [← e2] at hFe
    exact ⟨F, hFb, hFe⟩
  have keyT : ∀ m : ℕ, ∀ G : Finset E, ∃ F : Finset E,
      (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((m : ℝ) + 1))
        ∩ ks_rpol (𝕜 := 𝕜) ↑G = ∅) →
        ((∀ x ∈ F, ‖x‖ ≤ (δ * ((m : ℝ) + 1))⁻¹) ∧
          K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((m : ℝ) + 2))
            ∩ ks_rpol (𝕜 := 𝕜) (↑G ∪ ↑F) = ∅) := by
    intro m G
    by_cases h : K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E)
        (δ * ((m : ℝ) + 1)) ∩ ks_rpol (𝕜 := 𝕜) ↑G = ∅
    · obtain ⟨F, hFb, hFe⟩ := key m G h
      exact ⟨F, fun _ => ⟨hFb, hFe⟩⟩
    · exact ⟨∅, fun h' => (h h').elim⟩
  have hFchoice : ∃ Fchoice : ℕ → Finset E → Finset E, ∀ m : ℕ, ∀ G : Finset E,
      (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((m : ℝ) + 1))
        ∩ ks_rpol (𝕜 := 𝕜) ↑G = ∅) →
        ((∀ x ∈ Fchoice m G, ‖x‖ ≤ (δ * ((m : ℝ) + 1))⁻¹) ∧
          K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((m : ℝ) + 2))
            ∩ ks_rpol (𝕜 := 𝕜) (↑G ∪ ↑(Fchoice m G)) = ∅) :=
    ⟨fun m G => Classical.choose (keyT m G), fun m G => Classical.choose_spec (keyT m G)⟩
  obtain ⟨Fchoice, hFspec⟩ := hFchoice
  have hGseq : ∃ Gseq : ℕ → Finset E, Gseq 0 = ∅ ∧
      ∀ m, Gseq (m + 1) = Gseq m ∪ Fchoice m (Gseq m) :=
    ⟨fun m => Nat.rec (motive := fun _ => Finset E) ∅ (fun m Gm => Gm ∪ Fchoice m Gm) m,
      rfl, fun m => rfl⟩
  obtain ⟨Gseq, hG0, hGS⟩ := hGseq
  have hinv : ∀ m : ℕ, K ∩ WeakDual.toStrongDual ⁻¹'
      closedBall (0 : StrongDual 𝕜 E) (δ * ((m : ℝ) + 1))
        ∩ ks_rpol (𝕜 := 𝕜) ↑(Gseq m) = ∅ := by
    intro m
    induction m with
    | zero =>
      have hrpol_empty : ks_rpol (𝕜 := 𝕜) (∅ : Set E) = Set.univ := by
        ext φ
        simp [ks_rpol]
      rw [hG0, Finset.coe_empty, hrpol_empty, Set.inter_univ]
      simp only [Nat.cast_zero, zero_add, mul_one]
      exact hKδ
    | succ m ihm =>
      have hnext := (hFspec m (Gseq m)) ihm
      obtain ⟨_, hFe⟩ := hnext
      have e2 : ((m : ℝ) + 2) = ((((m + 1 : ℕ)) : ℝ) + 1) := by
        rw [Nat.cast_add_one]; ring
      rw [e2] at hFe
      rw [hGS m, Finset.coe_union]
      exact hFe
  have hFb : ∀ m : ℕ, ∀ x ∈ Fchoice m (Gseq m), ‖x‖ ≤ (δ * ((m : ℝ) + 1))⁻¹ := by
    intro m x hx
    exact ((hFspec m (Gseq m) (hinv m)).1) x hx
  have hmemU : ∀ m : ℕ, ∀ y ∈ Gseq m, ∃ i, i < m ∧ y ∈ Fchoice i (Gseq i) := by
    intro m
    induction m with
    | zero =>
      intro y hy
      rw [hG0] at hy
      exact absurd hy (Finset.notMem_empty y)
    | succ m ihm =>
      intro y hy
      rw [hGS m, Finset.mem_union] at hy
      cases hy with
      | inl h =>
        obtain ⟨i, hi, hiy⟩ := ihm y h
        exact ⟨i, by omega, hiy⟩
      | inr h => exact ⟨m, by omega, h⟩
  have hmemL : ∀ m : ℕ, ∀ j : ℕ, j < ((Fchoice m (Gseq m)).toList).length →
      ((Fchoice m (Gseq m)).toList).getD j 0 ∈ Fchoice m (Gseq m) := by
    intro m j hj
    rw [List.getD_eq_getElem _ _ hj]
    exact Finset.mem_toList.mp (List.getElem_mem hj)
  refine ⟨fun p : ℕ × ℕ => ((Fchoice p.1 (Gseq p.1)).toList.getD p.2 0), ?_, ?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (δ⁻¹ / ε)
    have hNε : δ⁻¹ < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
    have hM : (0 : ℝ) < ((((N + 1 : ℕ)) : ℝ)) := by exact_mod_cast Nat.succ_pos N
    have hδM : 0 < δ * ((((N + 1 : ℕ)) : ℝ)) := mul_pos hδ hM
    have hNN : (N : ℝ) ≤ ((((N + 1 : ℕ)) : ℝ)) := by
      rw [Nat.cast_add_one]
      have h0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have hbound : (δ * ((((N + 1 : ℕ)) : ℝ)))⁻¹ < ε := by
      rw [inv_lt_iff_one_lt_mul₀' hδM]
      calc (1 : ℝ) = δ * δ⁻¹ := (mul_inv_cancel₀ hδ.ne').symm
        _ < δ * ((N : ℝ) * ε) := mul_lt_mul_of_pos_left hNε hδ
        _ ≤ (δ * ((((N + 1 : ℕ)) : ℝ))) * ε := by
          calc δ * ((N : ℝ) * ε) = (δ * ε) * (N : ℝ) := by ring
            _ ≤ (δ * ε) * ((((N + 1 : ℕ)) : ℝ)) :=
              mul_le_mul_of_nonneg_left hNN (mul_nonneg hδ.le hε.le)
            _ = (δ * ((((N + 1 : ℕ)) : ℝ))) * ε := by ring
    have hfin : {p : ℕ × ℕ | ¬ dist (((Fchoice p.1 (Gseq p.1)).toList.getD p.2 0)) 0
        < ε}.Finite := by
      set S : Finset (ℕ × ℕ) := (Finset.range (N + 1)).biUnion
        (fun m => (Finset.range ((Fchoice m (Gseq m)).card)).image
          (fun j => (m, j))) with hS
      have hsub : {p : ℕ × ℕ | ¬ dist (((Fchoice p.1 (Gseq p.1)).toList.getD p.2 0)) 0
          < ε} ⊆ ↑S := by
        rintro ⟨m, j⟩ hj
        simp only [Set.mem_ofPred_eq, dist_zero_right] at hj
        have hj' : ε ≤ ‖((Fchoice m (Gseq m)).toList.getD j 0)‖ := not_lt.mp hj
        have hm : m < N + 1 := by
          by_contra hcon
          have hNm : N + 1 ≤ m := not_lt.mp hcon
          have hlt : ‖((Fchoice m (Gseq m)).toList.getD j 0)‖ < ε := by
            by_cases hjlen : j < ((Fchoice m (Gseq m)).toList).length
            · have hb := hFb m _ (hmemL m j hjlen)
              have hmono : (δ * ((m : ℝ) + 1))⁻¹ ≤ (δ * ((((N + 1 : ℕ)) : ℝ)))⁻¹ := by
                apply inv_anti₀ hδM
                apply mul_le_mul_of_nonneg_left _ hδ.le
                have hNm2 : N + 1 ≤ m + 1 := le_trans hNm (Nat.le_add_right m 1)
                exact_mod_cast hNm2
              exact lt_of_le_of_lt (le_trans hb hmono) hbound
            · have hx0 : ((Fchoice m (Gseq m)).toList.getD j 0) = 0 :=
                List.getD_eq_default _ _ (not_lt.mp hjlen)
              rw [hx0, norm_zero]
              exact hε
          exact absurd hj' (not_le.mpr hlt)
        have hjm : j < (Fchoice m (Gseq m)).card := by
          by_contra hcon
          have hjmle : (Fchoice m (Gseq m)).card ≤ j := not_lt.mp hcon
          have hx0 : ((Fchoice m (Gseq m)).toList.getD j 0) = 0 := by
            apply List.getD_eq_default _ _
            rw [Finset.length_toList]
            exact hjmle
          rw [hx0, norm_zero] at hj'
          exact absurd hj' (not_le.mpr hε)
        rw [Finset.mem_coe, hS, Finset.mem_biUnion]
        exact ⟨m, Finset.mem_range.mpr hm,
          Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjm, rfl⟩⟩
      exact Set.Finite.subset (Finset.finite_toSet S) hsub
    exact Filter.eventually_cofinite.mpr hfin
  · intro p
    obtain ⟨m, j⟩ := p
    change ‖((Fchoice m (Gseq m)).toList.getD j 0)‖ ≤ δ⁻¹
    by_cases hjlen : j < ((Fchoice m (Gseq m)).toList).length
    · have hb := hFb m _ (hmemL m j hjlen)
      have hle1 : (1 : ℝ) ≤ ((((m + 1 : ℕ)) : ℝ)) := by
        rw [Nat.cast_add_one]
        have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      have hδle : δ ≤ δ * ((((m + 1 : ℕ)) : ℝ)) :=
        le_mul_of_one_le_right hδ.le hle1
      have hback : (δ * ((((m + 1 : ℕ)) : ℝ)))⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hδle
      have hb' : ‖((Fchoice m (Gseq m)).toList.getD j 0)‖ ≤ (δ * ((m : ℝ) + 1))⁻¹ :=
        hb
      have hfw : (δ * ((m : ℝ) + 1))⁻¹ = (δ * ((((m + 1 : ℕ)) : ℝ)))⁻¹ := by
        rw [Nat.cast_add_one]
      rw [hfw] at hb'
      exact le_trans hb' hback
    · have hx0 : ((Fchoice m (Gseq m)).toList.getD j 0) = 0 :=
        List.getD_eq_default _ _ (not_lt.mp hjlen)
      rw [hx0, norm_zero]
      exact inv_nonneg.mpr hδ.le
  · intro φ hφ
    obtain ⟨N, hN⟩ := exists_nat_ge (‖WeakDual.toStrongDual φ‖ / δ)
    have hleN : ‖WeakDual.toStrongDual φ‖ ≤ δ * ((N : ℝ) + 1) := by
      have hle : ‖WeakDual.toStrongDual φ‖ ≤ δ * (N : ℝ) := by
        have h1 : ‖WeakDual.toStrongDual φ‖ / δ ≤ (N : ℝ) := hN
        rw [div_le_iff₀ hδ] at h1
        calc ‖WeakDual.toStrongDual φ‖ ≤ (N : ℝ) * δ := h1
          _ = δ * (N : ℝ) := by ring
      calc ‖WeakDual.toStrongDual φ‖ ≤ δ * (N : ℝ) := hle
        _ ≤ δ * ((N : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left _ hδ.le
          have h0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          linarith
    have hB : φ ∈ WeakDual.toStrongDual ⁻¹'
        closedBall (0 : StrongDual 𝕜 E) (δ * ((N : ℝ) + 1)) := by
      change WeakDual.toStrongDual φ ∈
        closedBall (0 : StrongDual 𝕜 E) (δ * ((N : ℝ) + 1))
      rw [mem_closedBall_zero_iff]
      exact hleN
    have hnotin : φ ∉ ks_rpol (𝕜 := 𝕜) ↑(Gseq N) := by
      intro hr
      have hmem : φ ∈ K ∩ WeakDual.toStrongDual ⁻¹'
          closedBall (0 : StrongDual 𝕜 E) (δ * ((N : ℝ) + 1))
            ∩ ks_rpol (𝕜 := 𝕜) ↑(Gseq N) :=
        ⟨⟨hφ, hB⟩, hr⟩
      rw [hinv N] at hmem
      exact notMem_empty φ hmem
    obtain ⟨y, hyG, hy1⟩ : ∃ y ∈ (↑(Gseq N) : Set E), 1 < RCLike.re (φ y) := by
      by_contra hcon
      apply hnotin
      change ∀ y ∈ (↑(Gseq N) : Set E), RCLike.re (φ y) ≤ 1
      intro y hy
      by_contra hle'
      have hlt : 1 < RCLike.re (φ y) := lt_of_not_ge hle'
      exact hcon ⟨y, hy, hlt⟩
    obtain ⟨i, _, hyF⟩ := hmemU N y (Finset.mem_coe.mp hyG)
    have hyL : y ∈ (Fchoice i (Gseq i)).toList := Finset.mem_toList.mpr hyF
    obtain ⟨j, hjlen, hjeq⟩ := List.mem_iff_getElem.mp hyL
    refine ⟨(i, j), ?_⟩
    change 1 < RCLike.re (φ (((Fchoice i (Gseq i)).toList.getD j 0)))
    have hxy : ((Fchoice i (Gseq i)).toList.getD j 0) = y := by
      rw [List.getD_eq_getElem _ _ hjlen]
      exact hjeq
    rw [hxy]
    exact hy1

/-- Real parts distribute over addition. -/
lemma ks_re_add {𝕜 : Type*} [RCLike 𝕜] (z w : 𝕜) :
    RCLike.re (z + w) = RCLike.re z + RCLike.re w := by
  have h := map_add (RCLike.reCLM (K := 𝕜)) z w
  rwa [RCLike.reCLM_apply] at h

end FunctionalAnalysis.BanachSpaceWanted
