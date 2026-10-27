import Mathlib
import Initialize.Tactic.Attr.Basic
open Module.End
open ContinuousLinearMap


noncomputable def highPart
  {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  (T : E →L[𝕜] E) (r : ℝ) : Submodule 𝕜 E :=
  ⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), eigenspace (T : Module.End 𝕜 E) μ

private lemma le_norm_sub_of_mem_eigenspace
  {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {T : E →L[𝕜] E} (hT' : (T : E →ₗ[𝕜] E).IsSymmetric)
  {μ ν : 𝕜} (hμν : μ ≠ ν) {r : ℝ} (hr : 0 ≤ r) (hμ : r ≤ ‖μ‖) (hν : r ≤ ‖ν‖)
  {e e' : E} (he : e ∈ eigenspace (T : Module.End 𝕜 E) μ) (he' : e' ∈ eigenspace (T : Module.End 𝕜 E) ν)
  (hne : ‖e‖ = 1) (hne' : ‖e'‖ = 1) : r ≤ ‖T e - T e'‖ := by
  have h0 : inner 𝕜 e e' = 0 := hT'.orthogonalFamily_eigenspaces hμν ⟨e, he⟩ ⟨e', he'⟩
  have horth : inner 𝕜 (μ • e) (ν • e') = 0 := by
    rw [inner_smul_left, inner_smul_right, h0]; simp
  have hTe : T e = μ • e := mem_eigenspace_iff.mp he
  have hTe' : T e' = ν • e' := mem_eigenspace_iff.mp he'
  rw [hTe, hTe']
  have hpy : ‖μ • e - ν • e'‖ * ‖μ • e - ν • e'‖ = ‖μ • e‖ * ‖μ • e‖ + ‖ν • e'‖ * ‖ν • e'‖ := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) (μ • e) (-(ν • e'))
      (by rw [inner_neg_right, horth, neg_zero])
    rwa [← sub_eq_add_neg, norm_neg] at this
  rw [norm_smul, norm_smul, hne, hne', mul_one, mul_one] at hpy
  have h1 : r * r ≤ ‖μ • e - ν • e'‖ * ‖μ • e - ν • e'‖ := by
    rw [hpy]; nlinarith [norm_nonneg μ, norm_nonneg ν]
  nlinarith [norm_nonneg (μ • e - ν • e'), h1]

private lemma finite_setOf_hasEigenvalue_le_norm
  {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {T : E →L[𝕜] E}
  (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) {r : ℝ} (hr : 0 < r) :
  {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 E) μ ∧ r ≤ ‖μ‖}.Finite := by
  by_contra hinf
  have hinf' : {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 E) μ ∧ r ≤ ‖μ‖}.Infinite := hinf
  let μ : ℕ → 𝕜 := fun n => (hinf'.natEmbedding _ n : 𝕜)
  have hμmem : ∀ n, HasEigenvalue (T : Module.End 𝕜 E) (μ n) ∧ r ≤ ‖μ n‖ := fun n => (hinf'.natEmbedding _ n).2
  have hμinj : Function.Injective μ := fun a b h =>
    (hinf'.natEmbedding _).injective (Subtype.ext h)
  have hex : ∀ n, ∃ e : E, e ∈ eigenspace (T : Module.End 𝕜 E) (μ n) ∧ ‖e‖ = 1 := by
    intro n
    obtain ⟨v, hv, hv0⟩ := (hμmem n).1.exists_hasEigenvector
    refine ⟨(‖v‖⁻¹ : 𝕜) • v, Submodule.smul_mem _ _ hv, ?_⟩
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  choose e he hne using hex
  have hsep : ∀ n m, n ≠ m → r ≤ ‖T (e n) - T (e m)‖ := fun n m hnm =>
    le_norm_sub_of_mem_eigenspace hT' (fun h => hnm (hμinj h)) hr.le (hμmem n).2 (hμmem m).2 (he n) (he m)
      (hne n) (hne m)
  have hK : IsCompact (closure (T '' Metric.closedBall (0 : E) 1)) := hT.isCompact_closure_image_closedBall 1
  have hin : ∀ n, T (e n) ∈ closure (T '' Metric.closedBall (0 : E) 1) := fun n =>
    subset_closure ⟨e n, by simp [hne n], rfl⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hin
  have hc : CauchySeq (fun n => T (e (φ n))) := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hc
  obtain ⟨N₀, hN₀⟩ := hc r hr
  have := hN₀ N₀ le_rfl (N₀ + 1) (by omega)
  rw [dist_eq_norm] at this
  exact absurd (hsep (φ N₀) (φ (N₀ + 1)) (fun h => by have := hφ.injective h; omega)) (not_le.mpr this)

private lemma finiteDimensional_highPart
  {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {T : E →L[𝕜] E}
  (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) {r : ℝ} (hr : 0 < r) :
  FiniteDimensional 𝕜 ↥(highPart T r) := by
  set M := {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 E) μ ∧ r ≤ ‖μ‖} with hM
  have hfin : M.Finite := finite_setOf_hasEigenvalue_le_norm hT hT' hr
  have : ∀ μ : 𝕜, μ ∈ hfin.toFinset → FiniteDimensional 𝕜 ↥(eigenspace (T : Module.End 𝕜 E) μ) := by
    intro μ hμ
    rw [Set.Finite.mem_toFinset] at hμ
    exact finite_dimensional_eigenspace hT μ (fun h => by
      have h2 : r ≤ ‖μ‖ := hμ.2
      rw [h, norm_zero] at h2; exact absurd h2 (not_le.mpr hr))
  have hle : highPart T r ≤ hfin.toFinset.sup fun μ => eigenspace (T : Module.End 𝕜 E) μ := by
    refine iSup₂_le fun μ hμ => ?_
    if h : HasEigenvalue (T : Module.End 𝕜 E) μ then
      exact Finset.le_sup (f := fun μ => eigenspace (T : Module.End 𝕜 E) μ)
      (hfin.mem_toFinset.mpr ⟨h, hμ⟩)
    else
      rw [hasEigenvalue_iff, not_ne_iff] at h
      rw [h]; apply bot_le
  have : ∀ i : { x // x ∈ hfin.toFinset }, FiniteDimensional 𝕜 ↥(eigenspace (T : Module.End 𝕜 E) i) :=
    fun i => this i i.2
  have : FiniteDimensional 𝕜 ↥(hfin.toFinset.sup fun μ => eigenspace (T : Module.End 𝕜 E) μ) := by
    rw [Finset.sup_eq_iSup]
    have e : (⨆ μ ∈ hfin.toFinset, eigenspace (T : Module.End 𝕜 E) μ) =
      ⨆ i : { x // x ∈ hfin.toFinset }, eigenspace (T : Module.End 𝕜 E) i := by
      rw [iSup_subtype']
    rw [e]
    exact Submodule.finiteDimensional_iSup _
  exact Submodule.finiteDimensional_of_le hle

private lemma apply_mem_iSup_eigenspace_ne_zero
  {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {T : E →L[𝕜] E} {u : E}
  (hu : u ∈ ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ) :
  T u ∈ ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ := by
  refine Submodule.iSup_induction _
    (motive := fun u => T u ∈ ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ) hu
    (fun μ x hx => ?_) (by simp) (fun x y hx hy => ?_)
  ·
    if hμ : μ = 0 then
      simp [hμ] at hx; simp [hx]
    else
      rw [iSup_pos hμ, mem_eigenspace_iff] at hx
      have hx' : T x = μ • x := hx
      rw [hx']
      refine Submodule.smul_mem _ μ (Submodule.mem_iSup_of_mem μ ?_)
      rw [iSup_pos hμ, mem_eigenspace_iff]
      show T x = μ • x
      exact hx'
  ·
    rw [map_add]; exact Submodule.add_mem _ hx hy

private lemma orthogonal_iSup_eigenspace_ne_zero_eq_ker
  {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {T : E →L[𝕜] E}
  (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
  (⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ)ᗮ = LinearMap.ker (T : E →ₗ[𝕜] E) := by
  set K : Submodule 𝕜 E := ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ with hK
  apply le_antisymm
  ·
    intro v hv
    have hinv : ∀ w ∈ Kᗮ, T w ∈ Kᗮ := by
      intro w hw
      rw [Submodule.mem_orthogonal] at hw ⊢
      intro u hu
      have e : inner 𝕜 u (T w) = inner 𝕜 ((T : E →ₗ[𝕜] E) u) w := (hT' u w).symm
      rw [e]
      exact hw _ (apply_mem_iSup_eigenspace_ne_zero hu)
    let S : ↥Kᗮ →L[𝕜] ↥Kᗮ := T.restrict hinv
    have hS_compact : IsCompactOperator S := hT.restrict' hinv
    have hS_symm : (S : ↥Kᗮ →ₗ[𝕜] ↥Kᗮ).IsSymmetric := hT'.restrict_invariant hinv
    have hS0 : S = 0 := by
      rw [← eq_zero_of_forall_hasEigenvalue_eq_zero hS_compact hS_symm]
      intro μ hμ
      by_contra hμ0
      rw [hasEigenvalue_iff] at hμ
      apply hμ
      rw [eq_bot_iff]
      intro w hw
      rw [mem_eigenspace_iff] at hw
      have hw' : ((S w : Kᗮ) : E) = ((μ • w : Kᗮ) : E) := congrArg Subtype.val hw
      have hwE : (w : E) ∈ eigenspace (T : Module.End 𝕜 E) μ := by
        rw [mem_eigenspace_iff]
        apply hw'
      have hwK : (w : E) ∈ K := by
        refine Submodule.mem_iSup_of_mem μ ?_
        rw [iSup_pos hμ0]; apply hwE
      have hw0 : (w : E) ∈ K ⊓ Kᗮ := ⟨hwK, w.2⟩
      rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hw0
      rw [Submodule.mem_bot]
      exact Subtype.ext hw0
    have h1 : ((S ⟨v, hv⟩ : Kᗮ) : E) = 0 := by rw [hS0]; rfl
    refine h1
  ·
    intro v hv
    have hv0 : v ∈ eigenspace (T : Module.End 𝕜 E) 0 := by
      rw [mem_eigenspace_iff, zero_smul]; apply hv
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.iSup_induction _ (motive := fun u => inner 𝕜 u v = 0) hu
      (fun μ x hx => ?_) (by simp) (fun x y hx hy => ?_)
    ·
      if hμ : μ = 0 then
        simp [hμ] at hx; simp [hx]
      else
        rw [iSup_pos hμ] at hx
        exact hT'.orthogonalFamily_eigenspaces hμ ⟨x, hx⟩ ⟨v, hv0⟩
    · rw [inner_add_left, hx, hy, add_zero]

private lemma highPart_sup_orthogonal_eq_top
  {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {T : E →L[𝕜] E}
  (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) {r : ℝ} (hr : 0 < r) :
  highPart T r ⊔ (highPart T r)ᗮ = ⊤ := by
  have := finiteDimensional_highPart hT hT' hr
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

private lemma map_highPart_le_of_commute
  {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {T S : E →L[𝕜] E}
  (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) (r : ℝ) :
  Submodule.map (S : E →ₗ[𝕜] E) (highPart T r) ≤ highPart T r := by
  unfold highPart
  rw [Submodule.map_iSup]
  refine iSup_mono fun μ => ?_
  rw [Submodule.map_iSup]
  refine iSup_mono fun hμ => ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_eigenspace_iff] at hx
  rw [mem_eigenspace_iff]
  have h := congrArg (fun A : E →L[𝕜] E => A x) hST
  simp only [coe_comp', Function.comp_apply] at h
  show (T : E →ₗ[𝕜] E) (S x) = μ • S x
  have : T (S x) = S (T x) := h.symm
  rw [ContinuousLinearMap.coe_coe, this, show (T x) = μ • x from hx, map_smul]

private lemma adjoint_comp_eq_of_isSymmetric
  {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {T S : E →L[𝕜] E}
  (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) :
  (adjoint S).comp T = T.comp (adjoint S) := by
  have hT : adjoint T = T := hT'.isSelfAdjoint.adjoint_eq
  have := congrArg adjoint hST
  rw [adjoint_comp, adjoint_comp, hT] at this
  apply this.symm

private lemma map_highPart_orthogonal_le_of_commute
  {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {T S : E →L[𝕜] E}
  (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) (r : ℝ) :
  Submodule.map (S : E →ₗ[𝕜] E) (highPart T r)ᗮ ≤ (highPart T r)ᗮ := by
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_orthogonal] at hy
  rw [Submodule.mem_orthogonal]
  intro x hx
  have hx' : adjoint S x ∈ highPart T r :=
    map_highPart_le_of_commute hT' (adjoint_comp_eq_of_isSymmetric hT' hST) r ⟨x, hx, rfl⟩
  rw [ContinuousLinearMap.coe_coe, ← adjoint_inner_left]
  exact hy _ hx'

private lemma iInf_highPart_orthogonal_eq_ker
  {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {T : E →L[𝕜] E}
  (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
  (⨅ (r : ℝ) (_ : 0 < r), (highPart T r)ᗮ) = LinearMap.ker (T : E →ₗ[𝕜] E) := by
  rw [← orthogonal_iSup_eigenspace_ne_zero_eq_ker hT hT']
  have e : (⨅ (r : ℝ) (_ : 0 < r), (highPart T r)ᗮ) = (⨆ (r : ℝ) (_ : 0 < r), highPart T r)ᗮ := by
    rw [← Submodule.iInf_orthogonal]
    refine iInf_congr fun r => ?_
    if hr : 0 < r then
      simp only [iInf_pos hr, iSup_pos hr]
    else
      simp only [iInf_neg hr, iSup_neg hr, Submodule.bot_orthogonal_eq_top]
  rw [e]
  congr 1
  apply le_antisymm
  ·
    refine iSup₂_le fun r hr => iSup₂_le fun μ hμ => ?_
    have hμ0 : μ ≠ 0 := fun h => by rw [h, norm_zero] at hμ; exact absurd hμ (not_le.mpr hr)
    refine le_iSup₂_of_le μ hμ0 le_rfl
  ·
    refine iSup₂_le fun μ hμ => ?_
    have hr : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
    refine le_iSup₂_of_le ‖μ‖ hr (le_iSup₂_of_le μ le_rfl le_rfl)

private lemma exists_inf_highPart_orthogonal_eq_bot_of_not_le_ker
  {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {T : E →L[𝕜] E}
  (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (X : Submodule 𝕜 E)
  (hX : ∀ r : ℝ, 0 < r → X ⊓ (highPart T r)ᗮ = ⊥ ∨ X ≤ (highPart T r)ᗮ)
  (hTX : ¬ X ≤ LinearMap.ker (T : E →ₗ[𝕜] E)) :
  ∃ r : ℝ, 0 < r ∧ X ⊓ (highPart T r)ᗮ = ⊥ ∧
    ∃ L : ↥X →ₗ[𝕜] ↥(highPart T r), Function.Injective L := by
  by_contra hcon
  push Not at hcon
  apply hTX
  rw [← iInf_highPart_orthogonal_eq_ker hT hT']
  refine le_iInf₂ fun r hr => ?_
  obtain h | h := hX r hr
  ·
    exfalso
    have := finiteDimensional_highPart hT hT' hr
    have hinj : Function.Injective
      (((highPart T r).orthogonalProjection : E →ₗ[𝕜] ↥(highPart T r)).comp X.subtype) := by
      intro a b hab
      apply Subtype.ext
      have h2 : (a : E) - b ∈ (highPart T r)ᗮ := by
        rw [← Submodule.orthogonalProjection_eq_zero_iff, map_sub, sub_eq_zero]
        apply hab
      have hmem : (a : E) - b ∈ X ⊓ (highPart T r)ᗮ := ⟨X.sub_mem a.2 b.2, h2⟩
      rw [h, Submodule.mem_bot, sub_eq_zero] at hmem
      apply hmem
    refine hcon r hr h _ hinj
  · exact h

private lemma le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal
  {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
  {T : E →L[𝕜] E}
  (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (X : Submodule 𝕜 E)
  (hX : ∀ r : ℝ, 0 < r → X ⊓ (highPart T r)ᗮ = ⊥ ∨ X ≤ (highPart T r)ᗮ) :
  X ≤ LinearMap.ker (T : E →ₗ[𝕜] E) ∨ FiniteDimensional 𝕜 ↥X := by
  if hTX : X ≤ LinearMap.ker (T : E →ₗ[𝕜] E) then
    exact Or.inl hTX
  else
    obtain ⟨r, hr, -, L, hL⟩ := exists_inf_highPart_orthogonal_eq_bot_of_not_le_ker hT hT' X hX hTX
    have := finiteDimensional_highPart hT hT' hr
    exact Or.inr (Module.Finite.of_injective L hL)
open Module.End in
/--
[ContinuousLinearMap_orthogonal_iSup_eigenspace_ne_zero_eq_ker](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ContinuousLinearMap_orthogonal_iSup_eigenspace_ne_zero_eq_ker.lean)
-/
@[path]
private lemma main
  [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {T : E →L[𝕜] E}
-- given
  (hT : IsCompactOperator T)
  (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
-- imply
  (⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ)ᗮ = LinearMap.ker (T : E →ₗ[𝕜] E) :=
-- proof
  orthogonal_iSup_eigenspace_ne_zero_eq_ker hT hT'


-- created on 2026-10-23
