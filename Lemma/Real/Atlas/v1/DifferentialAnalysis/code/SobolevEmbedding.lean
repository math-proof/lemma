import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
open MeasureTheory Filter Topology SobolevEmbedding SchwartzRepresentation
open scoped ZeroAtInfty
open scoped SchwartzMap


namespace SobolevEmbedding

/--
[schwartz_iteratedFDeriv_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma schwartz_iteratedFDeriv_tendsto_zero
  {n : ℕ}
  {φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ}
  {j : ℕ} :
-- imply
  Tendsto (fun x => iteratedFDeriv ℝ j (φ : EuclideanSpace ℝ (Fin n) → ℂ) x) (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
-- proof
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨C, hC_pos, hC⟩ := φ.decay 1 j
  rw [Filter.hasBasis_cocompact.eventually_iff]
  refine ⟨Metric.closedBall 0 (C / ε), isCompact_closedBall 0 _, fun x hx => ?_⟩
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hx
  push_neg at hx
  simp only [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)]
  have hx_pos : 0 < ‖x‖ := by linarith [div_nonneg (le_of_lt hC_pos) (le_of_lt hε)]
  have h := hC x; simp only [pow_one] at h
  calc ‖iteratedFDeriv ℝ j (φ : EuclideanSpace ℝ (Fin n) → ℂ) x‖
    ≤ C / ‖x‖ := by rwa [le_div_iff₀ hx_pos, mul_comm]
    _ < C / (C / ε) := div_lt_div_of_pos_left hC_pos (by positivity) hx
    _ = ε := by field_simp

end SobolevEmbedding

namespace SobolevEmbedding

/--
[tendsto_zero_of_tendstoUniformly_of_vanish'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma tendsto_zero_of_tendstoUniformly_of_vanish'
  [TopologicalSpace α]
  [SeminormedAddCommGroup E]
  {l : Filter ι}
  [l.NeBot]
  {F : ι → α → E}
  {g : α → E}
-- given
  (hunif : TendstoUniformly F g l)
  (hvanish : ∀ᶠ i in l, Tendsto (F i) (cocompact α) (𝓝 0)) :
-- imply
  Tendsto g (cocompact α) (𝓝 0) := by
-- proof
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  rw [Metric.tendstoUniformly_iff] at hunif
  obtain ⟨i, hi_unif, hi_vanish⟩ := (hunif (ε / 2) hε2).and hvanish |>.exists
  rw [Metric.tendsto_nhds] at hi_vanish
  apply (hi_vanish (ε / 2) hε2).mono
  intro x hx
  calc dist (g x) 0
    ≤ dist (g x) (F i x) + dist (F i x) 0 := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hi_unif x) hx
    _ = ε := by ring

end SobolevEmbedding

namespace SchwartzRepresentation

/--
[mem_multiIndicesBall_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma mem_multiIndicesBall_iff
  {n : ℕ}
  {n m : ℕ}
  {α : Fin n → ℕ} :
-- imply
  α ∈ multiIndicesBall n m ↔ multiIndexOrder α ≤ m := by
-- proof
  simp only [multiIndicesBall, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range, and_iff_right_iff_imp]
  intro hord i
  exact Nat.lt_succ_of_le (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)) hord)

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[iterSchwartzDerivCoord_map_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma iterSchwartzDerivCoord_map_add
  {n : ℕ}
  {j : Fin n}
  {k : ℕ}
  {φ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  iterSchwartzDerivCoord j k (φ + ψ) = iterSchwartzDerivCoord j k φ + iterSchwartzDerivCoord j k ψ := by
-- proof
  unfold iterSchwartzDerivCoord
  induction k generalizing φ ψ with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp_apply, LineDerivAdd.lineDerivOp_add]
    exact ih _ _

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[iterSchwartzDeriv_map_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma iterSchwartzDeriv_map_add
  {n : ℕ}
  {β : Fin n → ℕ}
  {φ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  iterSchwartzDeriv β (φ + ψ) = iterSchwartzDeriv β φ + iterSchwartzDeriv β ψ := by
-- proof
  unfold iterSchwartzDeriv
  induction (List.finRange n) with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons, ih]
    exact iterSchwartzDerivCoord_map_add j (β j) _ _

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[iterSchwartzDerivCoord_map_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma iterSchwartzDerivCoord_map_smul
  {n : ℕ}
  {j : Fin n}
  {k : ℕ}
  {c : ℂ}
  {φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  iterSchwartzDerivCoord j k (c • φ) = c • iterSchwartzDerivCoord j k φ := by
-- proof
  unfold iterSchwartzDerivCoord
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp_apply, LineDerivSMul.lineDerivOp_smul]
    exact ih _

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[iterSchwartzDeriv_map_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma iterSchwartzDeriv_map_smul
  {n : ℕ}
  {β : Fin n → ℕ}
  {c : ℂ}
  {φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  iterSchwartzDeriv β (c • φ) = c • iterSchwartzDeriv β φ := by
-- proof
  unfold iterSchwartzDeriv
  induction (List.finRange n) with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons, ih]
    exact iterSchwartzDerivCoord_map_smul j (β j) c _

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[schwartzToLp_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma schwartzToLp_add
  {n : ℕ}
  {α : Fin n → ℕ}
  {φ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  schwartzToLp n α (φ + ψ) = schwartzToLp n α φ + schwartzToLp n α ψ := by
-- proof
  simp only [schwartzToLp]
  have heq : (⇑(iterSchwartzDeriv α (φ + ψ)) : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume]
    (⇑(iterSchwartzDeriv α φ) + ⇑(iterSchwartzDeriv α ψ)) := by
    apply Filter.EventuallyEq.of_eq
    ext x
    rw [iterSchwartzDeriv_map_add]
    simp [SchwartzMap.add_apply]
  rw [MemLp.toLp_congr _ ((schwartzDerivMemLp n α φ).add (schwartzDerivMemLp n α ψ)) heq]
  exact MemLp.toLp_add _ _

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[schwartzToLp_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma schwartzToLp_smul
  {n : ℕ}
  {α : Fin n → ℕ}
  {c : ℂ}
  {φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  schwartzToLp n α (c • φ) = c • schwartzToLp n α φ := by
-- proof
  simp only [schwartzToLp]
  have heq : (⇑(iterSchwartzDeriv α (c • φ)) : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume]
    (c • ⇑(iterSchwartzDeriv α φ)) := by
    apply Filter.EventuallyEq.of_eq
    ext x
    rw [iterSchwartzDeriv_map_smul]
    simp [SchwartzMap.smul_apply]
  rw [MemLp.toLp_congr _ ((schwartzDerivMemLp n α φ).const_smul c) heq]
  exact MemLp.toLp_const_smul c _
end SchwartzProdLp

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[hahn_banach_riesz_product_l2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma hahn_banach_riesz_product_l2
  {n : ℕ}
  [MeasureSpace E]
  [MeasureTheory.SigmaFinite (MeasureTheory.volume : MeasureTheory.Measure E)]
  [DecidableEq ι]
  {A : Finset ι}
  [AddCommMonoid V]
  [Module ℂ V]
  {L : V →ₗ[ℂ] ℂ}
  {T : ι → V → E → ℂ}
  {C : ℝ}
-- given
  (hT_memLp : ∀ α ∈ A, ∀ v, MeasureTheory.MemLp (T α v) 2 MeasureTheory.volume)
  (hT_add : ∀ α ∈ A, ∀ v w, T α (v + w) =ᵐ[MeasureTheory.volume] T α v + T α w)
  (hT_smul : ∀ α ∈ A, ∀ (c : ℂ) v, T α (c • v) =ᵐ[MeasureTheory.volume] c • T α v)
  (hC : 0 < C)
  (hbound : ∀ v, ‖L v‖ ≤ C * ∑ α ∈ A, (∫ x, ‖T α v x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ)) :
-- imply
  ∃ (g : ι → E → ℂ), (∀ α ∈ A, MeasureTheory.MemLp (g α) 2 MeasureTheory.volume) ∧ ∀ v, L v = ∑ α ∈ A, ∫ x, g α x * T α v x := by
-- proof
  classical
  let H := PiLp 2 (fun (_ : ↥A) => ↥(Lp ℂ 2 (volume : Measure E)))
  let Φ : V →ₗ[ℂ] H :=
    { toFun := fun v => WithLp.toLp 2 (fun (i : ↥A) => (hT_memLp i.1 i.2 v).toLp _)
      map_add' := fun v w => by
        apply PiLp.ext; intro ⟨α, hα⟩
        change (hT_memLp α hα (v + w)).toLp _ =
          (hT_memLp α hα v).toLp _ + (hT_memLp α hα w).toLp _
        rw [MemLp.toLp_congr (hT_memLp α hα (v + w))
          ((hT_memLp α hα v).add (hT_memLp α hα w)) (hT_add α hα v w)]
        exact MemLp.toLp_add _ _
      map_smul' := fun c v => by
        apply PiLp.ext; intro ⟨α, hα⟩
        change (hT_memLp α hα (c • v)).toLp _ = c • (hT_memLp α hα v).toLp _
        rw [MemLp.toLp_congr (hT_memLp α hα (c • v))
          ((hT_memLp α hα v).const_smul c) (hT_smul α hα c v)]
        exact MemLp.toLp_const_smul c _ }
  have hΦ_comp_norm : ∀ v (i : ↥A),
    ‖(Φ v).ofLp i‖ = (∫ x, ‖T i.1 v x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
    intro v ⟨α, hα⟩
    show ‖(hT_memLp α hα v).toLp _‖ = _
    rw [Lp.norm_toLp, (hT_memLp α hα v).eLpNorm_eq_integral_rpow_norm
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)]
    simp only [ENNReal.toReal_ofNat]
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ _)]
    ring_nf
  have hbound' : ∀ v, ‖L v‖ ≤ C * ∑ i : ↥A, ‖(Φ v).ofLp i‖ := by
    intro v
    have hbd := hbound v
    rw [show ∑ α ∈ A, (∫ x, ‖T α v x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) =
      ∑ i : ↥A, ‖(Φ v).ofLp i‖ from by
        rw [← A.sum_coe_sort]; congr 1; ext ⟨α, hα⟩; exact (hΦ_comp_norm v ⟨α, hα⟩).symm] at hbd
    exact hbd
  have hker : ∀ v, Φ v = 0 → L v = 0 := by
    intro v hv
    have hzero : ∑ i : ↥A, ‖(Φ v).ofLp i‖ = 0 := by
      rw [hv]; simp [PiLp.zero_apply, WithLp.ofLp]
    have hbd := hbound' v
    rw [hzero, mul_zero] at hbd
    exact norm_eq_zero.mp (le_antisymm hbd (norm_nonneg _))
  have hwf : ∀ (v₁ v₂ : V), Φ v₁ = Φ v₂ → L v₁ = L v₂ := by
    intro v₁ v₂ heq
    have h : Φ (v₁ + (-1 : ℂ) • v₂) = 0 := by
      rw [Φ.map_add, Φ.map_smul]; simp [heq]
    have h0 := hker _ h
    have hL : L (v₁ + (-1 : ℂ) • v₂) = L v₁ - L v₂ := by
      rw [L.map_add, L.map_smul]
      simp [sub_eq_add_neg, neg_smul, one_smul]
    rw [hL] at h0
    exact sub_eq_zero.mp h0
  let ℓ_fun : ↥(LinearMap.range Φ) → ℂ := fun y => L (Classical.choose y.2)
  have hℓ_wf : ∀ (y : ↥(LinearMap.range Φ)) (v : V), Φ v = y.1 → ℓ_fun y = L v := by
    intro y v hv; exact hwf _ _ (by rw [Classical.choose_spec y.2, hv])
  let ℓ_lin : ↥(LinearMap.range Φ) →ₗ[ℂ] ℂ :=
    { toFun := ℓ_fun
      map_add' := fun a b => by
        have ha := Classical.choose_spec a.2
        have hb := Classical.choose_spec b.2
        have hab : Φ (Classical.choose a.2 + Classical.choose b.2) = (a : H) + b := by
          rw [Φ.map_add, ha, hb]
        have hkey := hwf _ _ (hab.trans (Classical.choose_spec (a + b).2).symm)
        simp only [ℓ_fun, L.map_add] at hkey ⊢
        exact hkey.symm
      map_smul' := fun c a => by
        have ha := Classical.choose_spec a.2
        have hca : Φ (c • Classical.choose a.2) = c • (a : H) := by
          rw [Φ.map_smul, ha]
        have hkey := hwf _ _ (hca.trans (Classical.choose_spec (c • a).2).symm)
        simp only [ℓ_fun, L.map_smul, RingHom.id_apply] at hkey ⊢
        exact hkey.symm }
  have hℓ_bound : ∀ y : ↥(LinearMap.range Φ), ‖ℓ_lin y‖ ≤
    (C * Real.sqrt A.card) * ‖(y : H)‖ := by
    intro ⟨y, hy⟩
    have hv := Classical.choose_spec hy
    show ‖L (Classical.choose hy)‖ ≤ _
    calc ‖L (Classical.choose hy)‖
      ≤ C * ∑ i : ↥A, ‖(Φ (Classical.choose hy)).ofLp i‖ := hbound' _
      _ = C * ∑ i : ↥A, ‖(⟨y, hy⟩ : ↥(LinearMap.range Φ)).1.ofLp i‖ := by
        congr 2; ext i; congr 1
        exact congr_fun (congr_arg WithLp.ofLp hv) i
      _ ≤ C * (Real.sqrt A.card * Real.sqrt (∑ i : ↥A,
        ‖(⟨y, hy⟩ : ↥(LinearMap.range Φ)).1.ofLp i‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ↥A) (fun _ => (1 : ℝ))
          (fun i => ‖(⟨y, hy⟩ : ↥(LinearMap.range Φ)).1.ofLp i‖)
        simp only [one_mul, one_pow, Finset.sum_const, Nat.smul_one_eq_cast,
          Finset.card_univ, Fintype.card_coe] at h
        exact h
      _ = (C * Real.sqrt A.card) * ‖(⟨y, hy⟩ : ↥(LinearMap.range Φ)).1‖ := by
        rw [PiLp.norm_eq_of_L2]; ring
  let ℓ_clm : ↥(LinearMap.range Φ) →L[ℂ] ℂ :=
    LinearMap.mkContinuous ℓ_lin (C * Real.sqrt A.card) hℓ_bound
  obtain ⟨L', hL'ext, _⟩ := exists_extension_norm_eq (LinearMap.range Φ) ℓ_clm
  set G := (InnerProductSpace.toDual ℂ H).symm L'
  refine ⟨fun α => if hα : α ∈ A then
    fun x => (starRingEnd ℂ) ((G.ofLp ⟨α, hα⟩ : E → ℂ) x) else 0, ?_, ?_⟩
  ·
    intro α hα
    simp only [dif_pos hα]
    have hmem : MemLp (↑↑(G.ofLp ⟨α, hα⟩) : E → ℂ) 2 volume := Lp.memLp _
    have heq : (fun x => (starRingEnd ℂ) ((G.ofLp ⟨α, hα⟩ : E → ℂ) x)) =
      star (↑↑(G.ofLp ⟨α, hα⟩) : E → ℂ) := by
        ext x; simp [Pi.star_apply, RCLike.star_def]
    rw [heq]; exact hmem.star
  ·
    intro v
    have hmem : Φ v ∈ LinearMap.range Φ := ⟨v, rfl⟩
    have hLv_eq : L v = L' (Φ v) := by
      have h1 : L' (Φ v) = L' ↑(⟨Φ v, hmem⟩ : ↥(LinearMap.range Φ)) := rfl
      rw [h1, hL'ext ⟨Φ v, hmem⟩]
      symm
      simp only [ℓ_clm, LinearMap.mkContinuous_apply]
      exact hℓ_wf ⟨Φ v, hmem⟩ v rfl
    have hLv_inner : L v = @inner ℂ _ _ G (Φ v) := by
      rw [hLv_eq, ← InnerProductSpace.toDual_apply_apply]
      simp [G, LinearIsometryEquiv.apply_symm_apply]
    rw [hLv_inner, PiLp.inner_apply, ← A.sum_coe_sort]
    congr 1; ext ⟨α, hα⟩
    rw [MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    exact (MemLp.coeFn_toLp (hT_memLp α hα v)).mono fun x hx => by
      simp only [dif_pos hα, RCLike.inner_apply]
      have hx' : (↑↑((Φ v).ofLp ⟨α, hα⟩) : E → ℂ) x = T α v x := hx
      rw [hx']; ring

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[schwartz_functional_l2_deriv_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma schwartz_functional_l2_deriv_bound
  {n : ℕ}
  {n : ℕ}
  {u : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] ℂ}
  {m : ℕ}
-- given
  (hbound : ∃ C : ℝ, 0 < C ∧ ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ‖u φ‖ ≤ C * ∑ α ∈ multiIndicesBall n m, (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ)) :
-- imply
  ∃ (g : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ), (∀ α, α ∈ multiIndicesBall n m → MeasureTheory.MemLp (g α) 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) ∧ ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)), u φ = ∑ α ∈ multiIndicesBall n m, ∫ x, g α x * (iterSchwartzDeriv α φ) x := by
-- proof
  classical
  obtain ⟨C, hC, hbd⟩ := hbound
  exact hahn_banach_riesz_product_l2
    (E := EuclideanSpace ℝ (Fin n))
    (ι := Fin n → ℕ)
    (A := multiIndicesBall n m)
    (V := 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u.toLinearMap)
    (fun α φ x => (iterSchwartzDeriv α φ) x)
    (fun α _ φ => schwartzDerivMemLp n α φ)
    (fun α _ φ ψ => by
      apply Filter.EventuallyEq.of_eq; ext x
      simp [iterSchwartzDeriv_map_add, SchwartzMap.add_apply, Pi.add_apply])
    (fun α _ c φ => by
      apply Filter.EventuallyEq.of_eq; ext x
      simp [iterSchwartzDeriv_map_smul, SchwartzMap.smul_apply, Pi.smul_apply])
    C hC hbd

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[l2_schwartz_pairing_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma l2_schwartz_pairing_bound
  {n : ℕ}
  {n j : ℕ}
  {g : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
-- imply
  ∃ C : ℝ, 0 < C ∧ ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ‖∫ x, g x * ψ x‖ ≤ C * ∑ β ∈ multiIndicesBall n j, (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
-- proof
  set A := (∫ x : EuclideanSpace ℝ (Fin n), ‖g x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) with hA_def
  refine ⟨A + 1, by linarith [Real.rpow_nonneg (integral_nonneg (fun x => by positivity) :
    (0:ℝ) ≤ ∫ x : EuclideanSpace ℝ (Fin n), ‖g x‖ ^ (2:ℝ)) (1/2 : ℝ)], fun ψ => ?_⟩
  have hderiv_zero : iterSchwartzDeriv (0 : Fin n → ℕ) ψ = ψ := by
    unfold iterSchwartzDeriv
    have h : ∀ (j : Fin n) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
      iterSchwartzDerivCoord j ((0 : Fin n → ℕ) j) φ = φ := by
      intro j φ
      simp only [Pi.zero_apply]
      unfold iterSchwartzDerivCoord
      simp [Function.iterate_zero]
    induction (List.finRange n) with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.foldr_cons]
      rw [ih, h]
  have h0_mem : (0 : Fin n → ℕ) ∈ multiIndicesBall n j := by
    rw [mem_multiIndicesBall_iff]
    simp [multiIndexOrder]
  have h_holder : ‖∫ x, g x * ψ x‖ ≤
    A * (∫ a : EuclideanSpace ℝ (Fin n),
      ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) a‖ ^ (2:ℝ)) ^ (1 / (2:ℝ)) := by
    calc ‖∫ x, g x * ψ x‖
      ≤ ∫ x, ‖g x * ψ x‖ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖g x‖ * ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) x‖ := by
        congr 1; ext x; exact Complex.norm_mul (g x) (ψ x)
      _ ≤ A * (∫ a, ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) a‖ ^ (2:ℝ)) ^ (1 / (2:ℝ)) := by
        have h22 : (2:ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
        have hg2 : MemLp g (ENNReal.ofReal 2) volume := by
          rwa [show ENNReal.ofReal 2 = 2 from by norm_num]
        have hψ2 : MemLp (ψ : EuclideanSpace ℝ (Fin n) → ℂ) (ENNReal.ofReal 2) volume := by
          rw [show ENNReal.ofReal 2 = 2 from by norm_num]
          exact ψ.memLp 2
        exact integral_mul_norm_le_Lp_mul_Lq h22 hg2 hψ2
  have h_term_eq : (∫ x : EuclideanSpace ℝ (Fin n),
    ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ^ (2:ℝ)) ^ (1/2 : ℝ) =
    (∫ x, ‖(iterSchwartzDeriv (0 : Fin n → ℕ) ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
    congr 1; congr 1; ext x; congr 1; congr 1
    have : (iterSchwartzDeriv (0 : Fin n → ℕ) ψ : EuclideanSpace ℝ (Fin n) → ℂ) x =
      (ψ : EuclideanSpace ℝ (Fin n) → ℂ) x := by
      rw [hderiv_zero]
    rw [this]
  have h_sum_nonneg : ∀ β ∈ multiIndicesBall n j,
    (0:ℝ) ≤ (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
    intro β _
    exact Real.rpow_nonneg (integral_nonneg (fun x => by positivity)) _
  have h_le_sum : (∫ x : EuclideanSpace ℝ (Fin n),
    ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ^ (2:ℝ)) ^ (1/2 : ℝ) ≤
    ∑ β ∈ multiIndicesBall n j,
      (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
    rw [h_term_eq]
    exact Finset.single_le_sum h_sum_nonneg h0_mem
  have hA_nonneg : (0:ℝ) ≤ A :=
    Real.rpow_nonneg (integral_nonneg (fun x => by positivity)) _
  have h_sum_nonneg' : (0:ℝ) ≤ ∑ β ∈ multiIndicesBall n j,
    (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) :=
    Finset.sum_nonneg h_sum_nonneg
  calc ‖∫ x, g x * ψ x‖
    ≤ A * (∫ a : EuclideanSpace ℝ (Fin n),
      ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) a‖ ^ (2:ℝ)) ^ (1 / (2:ℝ)) := h_holder
    _ ≤ A * ∑ β ∈ multiIndicesBall n j,
      (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
      apply mul_le_mul_of_nonneg_left h_le_sum hA_nonneg
    _ ≤ (A + 1) * ∑ β ∈ multiIndicesBall n j,
      (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
      apply mul_le_mul_of_nonneg_right (by linarith) h_sum_nonneg'

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[l2_schwartz_mul_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma l2_schwartz_mul_integrable
  {n : ℕ}
  {n : ℕ}
  {g : EuclideanSpace ℝ (Fin n) → ℂ}
  {ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
-- imply
  MeasureTheory.Integrable (fun x => g x * ψ x) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
-- proof
  hg.integrable_mul (ψ.memLp 2)

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[schwartz_lineDerivOp_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma schwartz_lineDerivOp_comm
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [SMulCommClass ℝ ℝ F]
  {v w : E}
  {φ : 𝓢(E, F)} :
-- imply
  LineDeriv.lineDerivOp v (LineDeriv.lineDerivOp w φ) = LineDeriv.lineDerivOp w (LineDeriv.lineDerivOp v φ) := by
-- proof
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hd : DifferentiableAt ℝ (fderiv ℝ (φ : E → F)) x := by
    convert (SchwartzMap.fderivCLM ℝ E F φ).differentiableAt using 1
  rw [show ⇑(LineDeriv.lineDerivOp w φ : 𝓢(E, F)) = fun y => fderiv ℝ (↑φ) y w from
    funext fun y => SchwartzMap.lineDerivOp_apply_eq_fderiv w φ y,
    fderiv_clm_apply hd (differentiableAt_const w),
    show ⇑(LineDeriv.lineDerivOp v φ : 𝓢(E, F)) = fun y => fderiv ℝ (↑φ) y v from
    funext fun y => SchwartzMap.lineDerivOp_apply_eq_fderiv v φ y,
    fderiv_clm_apply hd (differentiableAt_const v)]
  simp
  exact second_derivative_symmetric
    (f := (↑φ : E → F)) (f' := fderiv ℝ (↑φ))
    (fun y => φ.differentiableAt.hasFDerivAt) hd.hasFDerivAt v w

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[iterate_lineDerivOp_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma iterate_lineDerivOp_comm
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [SMulCommClass ℝ ℝ F]
  {v w : E}
  {k : ℕ}
  {φ : 𝓢(E, F)} :
-- imply
  (LineDeriv.lineDerivOp v)^[k] (LineDeriv.lineDerivOp w φ) = LineDeriv.lineDerivOp w ((LineDeriv.lineDerivOp v)^[k] φ) := by
-- proof
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp_apply]
    rw [schwartz_lineDerivOp_comm v w φ, ih]

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[iterate_iterate_lineDerivOp_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma iterate_iterate_lineDerivOp_comm
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [SMulCommClass ℝ ℝ F]
  {v w : E}
  {k m : ℕ}
  {φ : 𝓢(E, F)} :
-- imply
  (LineDeriv.lineDerivOp v)^[k] ((LineDeriv.lineDerivOp w)^[m] φ) = (LineDeriv.lineDerivOp w)^[m] ((LineDeriv.lineDerivOp v)^[k] φ) := by
-- proof
  induction m generalizing φ with
  | zero => simp
  | succ m ih =>
    simp only [Function.iterate_succ, Function.comp_apply]
    rw [ih (LineDeriv.lineDerivOp w φ)]
    congr 1
    exact iterate_lineDerivOp_comm v w k φ

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[iterSchwartzDerivCoord_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma iterSchwartzDerivCoord_comm
  {n : ℕ}
  {n : ℕ}
  {i j : Fin n}
  {a b : ℕ}
  {φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  iterSchwartzDerivCoord i a (iterSchwartzDerivCoord j b φ) = iterSchwartzDerivCoord j b (iterSchwartzDerivCoord i a φ) := by
-- proof
  simp only [iterSchwartzDerivCoord]
  exact iterate_iterate_lineDerivOp_comm _ _ a b φ

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[iterSchwartzDerivCoord_comm_foldr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma iterSchwartzDerivCoord_comm_foldr
  {n : ℕ}
  {n : ℕ}
  {j : Fin n}
  {k : ℕ}
  {γ : Fin n → ℕ}
  {l : List (Fin n)}
  {φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  iterSchwartzDerivCoord j k (l.foldr (fun i ψ => iterSchwartzDerivCoord i (γ i) ψ) φ) = l.foldr (fun i ψ => iterSchwartzDerivCoord i (γ i) ψ) (iterSchwartzDerivCoord j k φ) := by
-- proof
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [iterSchwartzDerivCoord_comm j i k (γ i), ih]

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[iterSchwartzDerivCoord_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma iterSchwartzDerivCoord_add
  {n : ℕ}
  {n : ℕ}
  {j : Fin n}
  {a b : ℕ}
  {φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  iterSchwartzDerivCoord j b (iterSchwartzDerivCoord j a φ) = iterSchwartzDerivCoord j (a + b) φ := by
-- proof
  simp only [iterSchwartzDerivCoord]
  rw [Nat.add_comm, ← Function.iterate_add_apply]

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[iterSchwartzDeriv_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma iterSchwartzDeriv_comp
  {n : ℕ}
  {n : ℕ}
  {α β : Fin n → ℕ}
  {φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  iterSchwartzDeriv β (iterSchwartzDeriv α φ) = iterSchwartzDeriv (α + β) φ := by
-- proof
  simp only [iterSchwartzDeriv]
  induction (List.finRange n) with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons, Pi.add_apply]
    conv_lhs => rw [← iterSchwartzDerivCoord_comm_foldr j (α j) β l]
    rw [iterSchwartzDerivCoord_add j (α j) (β j), ih]
    simp only [Pi.add_apply]

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[multiIndexOrder_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma multiIndexOrder_add
  {n : ℕ}
  {n : ℕ}
  {α β : Fin n → ℕ} :
-- imply
  multiIndexOrder (α + β) = multiIndexOrder α + multiIndexOrder β := by
-- proof
  simp only [multiIndexOrder, Pi.add_apply, Finset.sum_add_distrib]

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[multiIndicesBall_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma multiIndicesBall_mono
  {n : ℕ}
  {n : ℕ}
  {m m' : ℕ}
-- given
  (h : m ≤ m') :
-- imply
  multiIndicesBall n m ⊆ multiIndicesBall n m' := by
-- proof
  intro α hα
  rw [mem_multiIndicesBall_iff] at hα ⊢
  exact le_trans hα h

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[c0SchwartzPairing_sum_finset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma c0SchwartzPairing_sum_finset
  {n : ℕ}
  {s : Finset ι}
  {f : ι → C₀(EuclideanSpace ℝ (Fin n), ℂ)}
  {ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  c0SchwartzPairing (∑ i ∈ s, f i) ψ = ∑ i ∈ s, c0SchwartzPairing (f i) ψ := by
-- proof
  simp only [c0SchwartzPairing]
  have heval : ∀ x, (∑ i ∈ s, f i) x = ∑ i ∈ s, (f i) x := by
    intro x
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      simp only [Finset.sum_cons]
      rw [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, ih]
  simp_rw [heval, Finset.sum_mul]
  rw [integral_finset_sum]
  intro i _
  exact Integrable.bdd_mul (c := ‖(f i).toBCF‖) (ψ.integrable)
    ((f i).continuous.aestronglyMeasurable)
    (Filter.Eventually.of_forall
      (fun x => BoundedContinuousFunction.norm_coe_le_norm (f i).toBCF x))

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[monomial_zero_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma monomial_zero_eq
  {n : ℕ} :
-- imply
  monomial (0 : Fin n → ℕ) = fun _ => (1 : ℂ) := by
-- proof
  ext x
  simp [monomial, Pi.zero_apply]

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[c0SchwartzPairing_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma c0SchwartzPairing_zero
  {n : ℕ}
  {ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  c0SchwartzPairing (0 : C₀(EuclideanSpace ℝ (Fin n), ℂ)) ψ = 0 := by
-- proof
  simp [c0SchwartzPairing, ZeroAtInftyContinuousMap.coe_zero, Pi.zero_apply, zero_mul,
    MeasureTheory.integral_zero]

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[zero_mem_multiIndicesBall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma zero_mem_multiIndicesBall
  {n : ℕ}
  {n M : ℕ} :
-- imply
  (0 : Fin n → ℕ) ∈ multiIndicesBall n M := by
-- proof
  rw [mem_multiIndicesBall_iff]
  simp [multiIndexOrder, Pi.zero_apply]

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[representation_rewrite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma representation_rewrite
  {n : ℕ}
  {n M : ℕ}
  {v : (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  ∃ (m : ℕ) (f : (Fin n → ℕ) → (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)), ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)), (∑ γ ∈ multiIndicesBall n M, c0SchwartzPairing (v γ) (iterSchwartzDeriv γ φ)) = ∑ α ∈ multiIndicesBall n m, ∑ β ∈ multiIndicesBall n m, c0SchwartzPairing (f α β) (iterSchwartzDeriv β (SchwartzMap.smulLeftCLM ℂ (monomial α) φ)) := by
-- proof
  refine ⟨M, fun α β => if α = 0 then v β else 0, fun φ => ?_⟩
  have hsmul : SchwartzMap.smulLeftCLM ℂ (monomial (0 : Fin n → ℕ)) φ = φ := by
    rw [monomial_zero_eq, SchwartzMap.smulLeftCLM_const]
    simp
  change (∑ γ ∈ multiIndicesBall n M,
    c0SchwartzPairing (v γ) (iterSchwartzDeriv γ φ)) =
    ∑ α ∈ multiIndicesBall n M, ∑ β ∈ multiIndicesBall n M,
      c0SchwartzPairing (if α = 0 then v β else 0)
        (iterSchwartzDeriv β (SchwartzMap.smulLeftCLM ℂ (monomial α) φ))
  symm
  rw [Finset.sum_eq_single_of_mem (0 : Fin n → ℕ) (zero_mem_multiIndicesBall n M)
    (fun α _ hα => by
      simp only [hα, ite_false]
      exact Finset.sum_eq_zero fun β _ => c0SchwartzPairing_zero _)]
  simp [hsmul]

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[representation_rewrite_form2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
lemma representation_rewrite_form2
  {n : ℕ}
  {n M : ℕ}
  {v : (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  ∃ (m : ℕ) (g : (Fin n → ℕ) → (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)), ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)), (∑ γ ∈ multiIndicesBall n M, c0SchwartzPairing (v γ) (iterSchwartzDeriv γ φ)) = ∑ α ∈ multiIndicesBall n m, ∑ β ∈ multiIndicesBall n m, c0SchwartzPairing (g α β) (SchwartzMap.smulLeftCLM ℂ (monomial α) (iterSchwartzDeriv β φ)) := by
-- proof
  refine ⟨M, fun α β => if α = 0 then v β else 0, fun φ => ?_⟩
  have h0mem : (0 : Fin n → ℕ) ∈ multiIndicesBall n M := by
    rw [mem_multiIndicesBall_iff]
    simp [multiIndexOrder]
  have hmon0 : monomial (0 : Fin n → ℕ) = fun _ => (1 : ℂ) := by
    ext x; simp [monomial]
  have hsmul0 : ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
    SchwartzMap.smulLeftCLM ℂ (monomial (0 : Fin n → ℕ)) ψ = ψ := by
    intro ψ
    have hfun : monomial (0 : Fin n → ℕ) = fun (_ : EuclideanSpace ℝ (Fin n)) => (1 : ℂ) := hmon0
    simp [hfun]
  have hpair0 : ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
    c0SchwartzPairing (0 : C₀(EuclideanSpace ℝ (Fin n), ℂ)) ψ = 0 := by
    intro ψ; simp [c0SchwartzPairing, ZeroAtInftyContinuousMap.coe_zero]
  symm
  have step1 : ∀ α β,
    c0SchwartzPairing (if α = (0 : Fin n → ℕ) then v β else 0)
      (SchwartzMap.smulLeftCLM ℂ (monomial α) (iterSchwartzDeriv β φ)) =
    if α = 0 then c0SchwartzPairing (v β) (iterSchwartzDeriv β φ) else 0 := by
    intro α β
    split_ifs with h
    · subst h; rw [hsmul0]
    · exact hpair0 _
  simp_rw [step1]
  have key : ∀ α ∈ multiIndicesBall n M, α ≠ (0 : Fin n → ℕ) →
    (∑ β ∈ multiIndicesBall n M,
      if α = 0 then c0SchwartzPairing (v β) (iterSchwartzDeriv β φ) else 0) = 0 := by
    intro α _ hα
    simp [hα]
  rw [Finset.sum_eq_single_of_mem 0 h0mem key]
  simp
/-- **Schwartz representation theorem** (Melrose Thm 10.5, second form): every
tempered distribution `u ∈ 𝓢'(ℝ^n, ℂ)` is a finite sum
`u φ = ∑_{α,β} c0SchwartzPairing (v α β) (x^α · ∂^β φ)`
with `v α β` continuous and vanishing at infinity. -/
end SchwartzRepresentation


/--
[partialDeriv_iteratedFDeriv_memLp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
private lemma partialDeriv_iteratedFDeriv_memLp_eq
  {n : ℕ}
  {m : ℕ}
  {u : SobolevSpace n m}
  {j : Fin n}
  {i : ℕ}
-- given
  (hm : 1 ≤ m)
  (hi : i ≤ m - 1) :
-- imply
  MemLp (fun x => iteratedFDeriv ℝ i (fun y => fderiv ℝ u.toFun y (EuclideanSpace.single j 1)) x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
-- proof
  apply SobolevEmbedding.partialDeriv_iteratedFDeriv_memLp hm u j i hi

/--
[schwartzDerivMemLp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean)
-/
@[path]
private lemma schwartzDerivMemLp_eq
  {n : ℕ}
  {n : ℕ}
  {α : Fin n → ℕ}
  {φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  MemLp ((iterSchwartzDeriv α φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : EuclideanSpace ℝ (Fin n) → ℂ) 2 volume := by
-- proof
  apply SchwartzRepresentation.schwartzDerivMemLp n α φ


-- created on 2026-10-23
