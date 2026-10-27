import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Graph.MaxFlowMinCut
open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted


namespace MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/--
[cutFlow_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MaxFlowMinCut.lean)
-/
@[path]
lemma cutFlow_eq
  [Fintype V] [DecidableEq V]
  {s t : V}
  {f : V → V → ℝ}
  {S : Finset V}
-- given
  (hcons : ∀ v, v ≠ s → v ≠ t → ∑ u : V, f u v = ∑ w : V, f v w)
  (hs : s ∈ S)
  (ht : t ∉ S) :
-- imply
  flowValue s f = (∑ u ∈ S, ∑ v ∈ Finset.univ \ S, f u v) -
    (∑ u ∈ S, ∑ v ∈ Finset.univ \ S, f v u) := by
-- proof
  have hsplit_out : ∀ v : V, (∑ w : V, f v w) =
    (∑ w ∈ S, f v w) + ∑ w ∈ Finset.univ \ S, f v w := by
    intro v
    have h := Finset.sum_sdiff (Finset.subset_univ S) (f := fun w => f v w)
    rwa [add_comm]
  have hsplit_in : ∀ v : V, (∑ u : V, f u v) =
    (∑ u ∈ S, f u v) + ∑ u ∈ Finset.univ \ S, f u v := by
    intro v
    have h := Finset.sum_sdiff (Finset.subset_univ S) (f := fun u => f u v)
    rwa [add_comm]
  have hrest : ∑ v ∈ S.erase s, ((∑ w : V, f v w) - (∑ u : V, f u v)) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [Finset.mem_erase] at hv
    exact sub_eq_zero.mpr (hcons v hv.1 (fun heq => ht (heq ▸ hv.2))).symm
  have hsum : ∑ v ∈ S, ((∑ w : V, f v w) - (∑ u : V, f u v)) = flowValue s f := by
    rw [← Finset.add_sum_erase S _ hs, hrest, add_zero]
    rfl
  have hexpand : ∑ v ∈ S, ((∑ w : V, f v w) - (∑ u : V, f u v)) =
    ((∑ v ∈ S, ∑ w ∈ S, f v w) + (∑ u ∈ S, ∑ v ∈ Finset.univ \ S, f u v)) -
    ((∑ v ∈ S, ∑ u ∈ S, f u v) + (∑ u ∈ S, ∑ v ∈ Finset.univ \ S, f v u)) := by
    have h1 : ∀ v : V, ((∑ w : V, f v w) - (∑ u : V, f u v)) =
      ((∑ w ∈ S, f v w) + ∑ w ∈ Finset.univ \ S, f v w) -
      ((∑ u ∈ S, f u v) + ∑ u ∈ Finset.univ \ S, f u v) := by
      intro v
      rw [hsplit_out v, hsplit_in v]
    rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_sub_distrib]
    congr 1 <;> rw [Finset.sum_add_distrib]
  have hSS : (∑ v ∈ S, ∑ w ∈ S, f v w) = (∑ v ∈ S, ∑ u ∈ S, f u v) := Finset.sum_comm
  rwa [hexpand, hSS, add_sub_add_left_eq_sub] at hsum

end MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

namespace MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/--
[flowValue_le_cutCapacity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MaxFlowMinCut.lean)
-/
@[path]
lemma flowValue_le_cutCapacity
  [Fintype V] [DecidableEq V]
  {cap : V → V → ℝ}
  {s t : V}
  {f : V → V → ℝ}
  {S : Finset V}
-- given
  (hf : IsFeasibleFlow cap s t f)
  (hS : IsSTCut s t S) :
-- imply
  flowValue s f ≤ cutCapacity cap S := by
-- proof
  obtain ⟨hs, ht⟩ := hS
  rw [cutFlow_eq s t f hf.2.2 S hs ht]
  obtain ⟨h0, hcaple, hcons⟩ := hf
  unfold cutCapacity
  have hle : (∑ u ∈ S, ∑ v ∈ Finset.univ \ S, f u v) ≤
    ∑ u ∈ S, ∑ v ∈ Finset.univ \ S, cap u v := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    exact hcaple u v
  have hnn : 0 ≤ ∑ u ∈ S, ∑ v ∈ Finset.univ \ S, f v u := by
    apply Finset.sum_nonneg
    intro u _
    apply Finset.sum_nonneg
    intro v _
    exact h0 v u
  linarith

end MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

namespace MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/--
[feasible_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MaxFlowMinCut.lean)
-/
@[path]
private lemma feasible_isCompact {V : Type*} [Fintype V] [DecidableEq V]
  (cap : V → V → ℝ) (s t : V) :
  IsCompact {f : V → V → ℝ | IsFeasibleFlow cap s t f} := by
  have hE : IsCompact (Set.pi Set.univ
    (fun u : V => Set.pi Set.univ (fun v : V => Set.Icc 0 (cap u v)))) :=
    isCompact_univ_pi (fun u => isCompact_univ_pi (fun v => isCompact_Icc))
  have hC : IsClosed (⋂ v : V, ⋂ _ : v ≠ s, ⋂ _ : v ≠ t,
    {f : V → V → ℝ | (∑ u : V, f u v) = ∑ w : V, f v w}) := by
    apply isClosed_iInter
    intro v
    apply isClosed_iInter
    intro _
    apply isClosed_iInter
    intro _
    apply isClosed_eq
    · exact continuous_finsetSum Finset.univ
      (fun u _ => (continuous_apply v).comp (continuous_apply u))
    · exact continuous_finsetSum Finset.univ
      (fun w _ => (continuous_apply w).comp (continuous_apply v))
  have hsub : {f : V → V → ℝ | IsFeasibleFlow cap s t f} =
    (Set.pi Set.univ (fun u : V => Set.pi Set.univ (fun v : V => Set.Icc 0 (cap u v)))) ∩
    (⋂ v : V, ⋂ _ : v ≠ s, ⋂ _ : v ≠ t,
      {f : V → V → ℝ | (∑ u : V, f u v) = ∑ w : V, f v w}) := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_Icc, Set.mem_iInter]
    constructor
    · rintro ⟨h0, hle, hcons⟩
      exact ⟨fun u v => ⟨h0 u v, hle u v⟩, fun v hvs hvt => hcons v hvs hvt⟩
    · rintro ⟨h0le, hcons⟩
      exact ⟨fun u v => (h0le u v).1, fun u v => (h0le u v).2,
        fun v hvs hvt => hcons v hvs hvt⟩
  rw [hsub]
  exact hE.inter_right hC

end MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

namespace MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/--
[continuous_flowValue](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MaxFlowMinCut.lean)
-/
@[path]
private lemma continuous_flowValue {V : Type*} [Fintype V] [DecidableEq V] (s : V) :
  Continuous (fun f : V → V → ℝ => flowValue s f) := by
  unfold flowValue
  apply Continuous.sub
  · exact continuous_finsetSum Finset.univ
    (fun v _ => (continuous_apply v).comp (continuous_apply s))
  · exact continuous_finsetSum Finset.univ
    (fun u _ => (continuous_apply s).comp (continuous_apply u))

end MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

namespace MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/--
[exists_max_flow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MaxFlowMinCut.lean)
-/
@[path]
private lemma exists_max_flow {V : Type*} [Fintype V] [DecidableEq V]
  (cap : V → V → ℝ) (hcap : ∀ u v, 0 ≤ cap u v) (s t : V) :
  ∃ f : V → V → ℝ, IsFeasibleFlow cap s t f ∧
    ∀ f' : V → V → ℝ, IsFeasibleFlow cap s t f' → flowValue s f' ≤ flowValue s f := by
  have hne : {f : V → V → ℝ | IsFeasibleFlow cap s t f}.Nonempty := by
    refine ⟨0, fun u v => le_refl 0, fun u v => hcap u v, fun v _ _ => by simp⟩
  obtain ⟨f, hmem, hmax⟩ :=
    (feasible_isCompact cap s t).exists_isMaxOn hne (continuous_flowValue s).continuousOn
  exact ⟨f, hmem, fun f' hf' => hmax hf'⟩

end MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

namespace MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/--
[reachable_extend](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MaxFlowMinCut.lean)
-/
@[path]
private lemma reachable_extend {V : Type*} [Fintype V] [DecidableEq V]
  (cap : V → V → ℝ) (s : V) (f : V → V → ℝ) (u w : V)
  (hu : ReachableFrom cap s f u)
  (huw : f u w < cap u w ∨ 0 < f w u) :
  ReachableFrom cap s f w := by
  obtain ⟨k, v, h0v, hstepv, hkv⟩ := hu
  refine ⟨k + 1, Function.update v (k + 1) w, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (show (0 : ℕ) ≠ k + 1 by omega)]
    exact h0v
  · intro i hi
    obtain heq | hlt := eq_or_lt_of_le (show i ≤ k by omega)
    · rw [heq]
      have e1 : Function.update v (k + 1) w k = v k :=
        Function.update_of_ne (show k ≠ k + 1 by omega) _ _
      have e2 : Function.update v (k + 1) w (k + 1) = w := Function.update_self _ _ _
      rwa [e1, e2, hkv]
    · have e1 : Function.update v (k + 1) w i = v i :=
      Function.update_of_ne (show i ≠ k + 1 by omega) _ _
      have e2 : Function.update v (k + 1) w (i + 1) = v (i + 1) :=
        Function.update_of_ne (show i + 1 ≠ k + 1 by omega) _ _
      rw [e1, e2]
      exact hstepv i hlt
  · exact Function.update_self _ _ _

end MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

namespace MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/--
[exists_augmenting_flow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MaxFlowMinCut.lean)
-/
@[path]
private lemma exists_augmenting_flow {V : Type*} [Fintype V] [DecidableEq V]
  (cap : V → V → ℝ) (s t : V) (hst : s ≠ t)
  (f : V → V → ℝ) (hf : IsFeasibleFlow cap s t f)
  (n : ℕ) (vv : ℕ → V) (hstart : vv 0 = s)
  (hstep : ∀ i, i < n →
    f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)) ∨
    0 < f (vv (i + 1)) (vv i))
  (hend : vv n = t) :
  ∃ f' : V → V → ℝ, IsFeasibleFlow cap s t f' ∧ flowValue s f < flowValue s f' := by
  classical
  obtain ⟨h0, hle, hcons⟩ := hf
  have hn : 1 ≤ n := by
    obtain rfl | hpos := Nat.eq_zero_or_pos n
    · exact absurd (hstart.symm.trans hend) hst
    · exact hpos
  have hnpos : n ≠ 0 := by omega
  set gap : ℕ → ℝ := fun i =>
    if f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))
    then cap (vv i) (vv (i + 1)) - f (vv i) (vv (i + 1))
    else f (vv (i + 1)) (vv i) with hgap
  have hgap_pos : ∀ i, i < n → 0 < gap i := by
    intro i hi
    have h := hstep i hi
    by_cases hc : f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))
    · simp only [hgap, ite_eq_left hc]
      exact sub_pos.mpr hc
    · simp only [hgap, ite_eq_right hc]
      exact h.resolve_left hc
  have hIm_nonempty : (Finset.image gap (Finset.range n)).Nonempty := by
    rwa [Finset.image_nonempty, Finset.nonempty_range_iff]
  set m : ℝ := (Finset.image gap (Finset.range n)).min' hIm_nonempty with hm
  have hm_pos : 0 < m := by
    obtain ⟨i, hi, hmi⟩ := Finset.mem_image.mp (Finset.min'_mem _ hIm_nonempty)
    have hpos := hgap_pos i (Finset.mem_range.mp hi)
    rwa [hm, ← hmi]
  have hm_le : ∀ i, i ∈ Finset.range n → m ≤ gap i := by
    intro i hi
    rw [hm]
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem gap hi)
  set δ : ℝ := m / ((n : ℝ) + 1) with hδ
  have hδ_pos : 0 < δ := by
    simp only [hδ]
    exact div_pos hm_pos (by positivity)
  have hfrac : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    exact le_add_of_nonneg_right zero_le_one
  have hnnδ : (n : ℝ) * δ ≤ m := by
    calc (n : ℝ) * δ = m * ((n : ℝ) / ((n : ℝ) + 1)) := by simp only [hδ]; ring
      _ ≤ m * 1 := mul_le_mul_of_nonneg_left hfrac (le_of_lt hm_pos)
      _ = m := mul_one m
  set d : ℕ → V → V → ℝ := fun i a b =>
    if vv i = a ∧ vv (i + 1) = b ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)) then δ
    else if vv i = b ∧ vv (i + 1) = a ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)) then -δ
    else 0 with hd
  set Δ : V → V → ℝ := fun a b => ∑ i ∈ Finset.range n, d i a b with hΔ
  set f' : V → V → ℝ := fun a b => f a b + Δ a b with hf'
  have hd_ind : ∀ i a b, d i a b =
    (if vv i = a ∧ vv (i + 1) = b ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)) then δ else
      (0 : ℝ)) -
    (if vv i = b ∧ vv (i + 1) = a ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)) then δ else
      (0 : ℝ)) := by
    intro i a b
    simp only [hd]
    by_cases h1 : (vv i = a ∧ vv (i + 1) = b ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)))
    · simp only [ite_eq_left h1]
      have h2 : ¬(vv i = b ∧ vv (i + 1) = a ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))) :=
        fun h => h.2.2 h1.2.2
      simp only [ite_eq_right h2, sub_zero]
    · simp only [ite_eq_right h1]
      by_cases h2 : (vv i = b ∧ vv (i + 1) = a ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)))
      · simp only [ite_eq_left h2, zero_sub]
      · simp only [ite_eq_right h2, sub_zero]
  have hout1 : ∀ i c, (∑ b : V, (if vv i = c ∧ vv (i + 1) = b ∧ f (vv i) (vv (i + 1)) < cap (vv i)
    (vv (i + 1)) then δ else (0 : ℝ))) =
    (if vv i = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)) then δ else 0) := by
    intro i c
    by_cases h : vv i = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))
    · rw [ite_eq_left h, Finset.sum_eq_single (vv (i + 1))]
      · rw [ite_eq_left ⟨h.1, rfl, h.2⟩]
      · intro b _ hb
        rw [ite_eq_right]
        exact fun hcon => hb hcon.2.1.symm
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    · rw [ite_eq_right h]
      apply Finset.sum_eq_zero
      intro b _
      rw [ite_eq_right]
      exact fun hcon => h ⟨hcon.1, hcon.2.2⟩
  have hout2 : ∀ i c, (∑ b : V, (if vv i = b ∧ vv (i + 1) = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i)
    (vv (i + 1)) then δ else (0 : ℝ))) =
    (if vv (i + 1) = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)) then δ else 0) := by
    intro i c
    by_cases h : vv (i + 1) = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))
    · rw [ite_eq_left h, Finset.sum_eq_single (vv i)]
      · rw [ite_eq_left ⟨rfl, h.1, h.2⟩]
      · intro b _ hb
        rw [ite_eq_right]
        exact fun hcon => hb hcon.1.symm
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    · rw [ite_eq_right h]
      apply Finset.sum_eq_zero
      intro b _
      rw [ite_eq_right]
      exact fun hcon => h ⟨hcon.2.1, hcon.2.2⟩
  have hin1 : ∀ i c, (∑ u : V, (if vv i = u ∧ vv (i + 1) = c ∧ f (vv i) (vv (i + 1)) < cap (vv i)
    (vv (i + 1)) then δ else (0 : ℝ))) =
    (if vv (i + 1) = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)) then δ else 0) := by
    intro i c
    by_cases h : vv (i + 1) = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))
    · rw [ite_eq_left h, Finset.sum_eq_single (vv i)]
      · rw [ite_eq_left ⟨rfl, h.1, h.2⟩]
      · intro b _ hb
        rw [ite_eq_right]
        exact fun hcon => hb hcon.1.symm
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    · rw [ite_eq_right h]
      apply Finset.sum_eq_zero
      intro b _
      rw [ite_eq_right]
      exact fun hcon => h ⟨hcon.2.1, hcon.2.2⟩
  have hin2 : ∀ i c, (∑ u : V, (if vv i = c ∧ vv (i + 1) = u ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i)
    (vv (i + 1)) then δ else (0 : ℝ))) =
    (if vv i = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)) then δ else 0) := by
    intro i c
    by_cases h : vv i = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))
    · rw [ite_eq_left h, Finset.sum_eq_single (vv (i + 1))]
      · rw [ite_eq_left ⟨h.1, rfl, h.2⟩]
      · intro b _ hb
        rw [ite_eq_right]
        exact fun hcon => hb hcon.2.1.symm
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    · rw [ite_eq_right h]
      apply Finset.sum_eq_zero
      intro b _
      rw [ite_eq_right]
      exact fun hcon => h ⟨hcon.1, hcon.2.2⟩
  have hper : ∀ i c,
    (((if (vv i = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))) then δ else (0 : ℝ)) -
    (if (vv (i + 1) = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))) then δ else 0)) -
    ((if (vv (i + 1) = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))) then δ else 0) -
    (if (vv i = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))) then δ else 0))) =
    (if (vv i = c) then δ else 0) - (if (vv (i + 1) = c) then δ else 0) := by
    intro i c
    by_cases hvc : vv i = c <;> by_cases hwc : vv (i + 1) = c <;>
      by_cases hlt : f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))
    · rw [ite_eq_left (show (vv i = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))) from
      ⟨hvc, hlt⟩),
      ite_eq_right (show ¬((vv (i + 1) = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))))
        from fun h => h.2 hlt),
      ite_eq_left (show (vv (i + 1) = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))) from
        ⟨hwc, hlt⟩),
      ite_eq_right (show ¬((vv i = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)))) from
        fun h => h.2 hlt),
      ite_eq_left (show (vv i = c) from hvc),
      ite_eq_left (show (vv (i + 1) = c) from hwc)]; ring
    · rw [ite_eq_right (show ¬((vv i = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)))) from
      fun h => hlt h.2),
      ite_eq_left (show (vv (i + 1) = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))) from
        ⟨hwc, hlt⟩),
      ite_eq_right (show ¬((vv (i + 1) = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))))
        from fun h => hlt h.2),
      ite_eq_left (show (vv i = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))) from
        ⟨hvc, hlt⟩),
      ite_eq_left (show (vv i = c) from hvc),
      ite_eq_left (show (vv (i + 1) = c) from hwc)]; ring
    · rw [ite_eq_left (show (vv i = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))) from
      ⟨hvc, hlt⟩),
      ite_eq_right (show ¬((vv (i + 1) = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))))
        from fun h => hwc h.1),
      ite_eq_right (show ¬((vv (i + 1) = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))))
        from fun h => hwc h.1),
      ite_eq_right (show ¬((vv i = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)))) from
        fun h => h.2 hlt),
      ite_eq_left (show (vv i = c) from hvc),
      ite_eq_right (show ¬((vv (i + 1) = c)) from hwc)]; ring
    · rw [ite_eq_right (show ¬((vv i = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)))) from
      fun h => hlt h.2),
      ite_eq_right (show ¬((vv (i + 1) = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))))
        from fun h => hwc h.1),
      ite_eq_right (show ¬((vv (i + 1) = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))))
        from fun h => hwc h.1),
      ite_eq_left (show (vv i = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))) from
        ⟨hvc, hlt⟩),
      ite_eq_left (show (vv i = c) from hvc),
      ite_eq_right (show ¬((vv (i + 1) = c)) from hwc)]; ring
    · rw [ite_eq_right (show ¬((vv i = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)))) from
      fun h => hvc h.1),
      ite_eq_right (show ¬((vv (i + 1) = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))))
        from fun h => h.2 hlt),
      ite_eq_left (show (vv (i + 1) = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))) from
        ⟨hwc, hlt⟩),
      ite_eq_right (show ¬((vv i = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)))) from
        fun h => hvc h.1),
      ite_eq_right (show ¬((vv i = c)) from hvc),
      ite_eq_left (show (vv (i + 1) = c) from hwc)]; ring
    · rw [ite_eq_right (show ¬((vv i = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)))) from
      fun h => hvc h.1),
      ite_eq_left (show (vv (i + 1) = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))) from
        ⟨hwc, hlt⟩),
      ite_eq_right (show ¬((vv (i + 1) = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))))
        from fun h => hlt h.2),
      ite_eq_right (show ¬((vv i = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)))) from
        fun h => hvc h.1),
      ite_eq_right (show ¬((vv i = c)) from hvc),
      ite_eq_left (show (vv (i + 1) = c) from hwc)]; ring
    · rw [ite_eq_right (show ¬((vv i = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)))) from
      fun h => hvc h.1),
      ite_eq_right (show ¬((vv (i + 1) = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))))
        from fun h => hwc h.1),
      ite_eq_right (show ¬((vv (i + 1) = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))))
        from fun h => hwc h.1),
      ite_eq_right (show ¬((vv i = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)))) from
        fun h => h.2 hlt),
      ite_eq_right (show ¬((vv i = c)) from hvc),
      ite_eq_right (show ¬((vv (i + 1) = c)) from hwc)]; ring
    · rw [ite_eq_right (show ¬((vv i = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)))) from
      fun h => hvc h.1),
      ite_eq_right (show ¬((vv (i + 1) = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))))
        from fun h => hwc h.1),
      ite_eq_right (show ¬((vv (i + 1) = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))))
        from fun h => hwc h.1),
      ite_eq_right (show ¬((vv i = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)))) from
        fun h => hvc h.1),
      ite_eq_right (show ¬((vv i = c)) from hvc),
      ite_eq_right (show ¬((vv (i + 1) = c)) from hwc)]; ring
  have hout : ∀ c, (∑ b, Δ c b) =
    ∑ i ∈ Finset.range n, ((if vv i = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)) then δ
      else (0 : ℝ)) -
      (if vv (i + 1) = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)) then δ else 0)) := by
    intro c
    simp only [hΔ]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hd_ind]
    rw [Finset.sum_sub_distrib, hout1 i c, hout2 i c]
  have hin : ∀ c, (∑ u, Δ u c) =
    ∑ i ∈ Finset.range n, ((if vv (i + 1) = c ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))
      then δ else (0 : ℝ)) -
      (if vv i = c ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1)) then δ else 0)) := by
    intro c
    simp only [hΔ]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hd_ind]
    rw [Finset.sum_sub_distrib, hin1 i c, hin2 i c]
  have hbal : ∀ c, (∑ b, Δ c b) - (∑ u, Δ u c) =
    (if vv 0 = c then δ else (0 : ℝ)) - (if vv n = c then δ else 0) := by
    intro c
    rw [hout c, hin c, ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun i _ => hper i c)]
    have htel : ∀ k, (∑ i ∈ Finset.range k,
      ((if vv i = c then δ else (0 : ℝ)) - (if vv (i + 1) = c then δ else 0))) =
      (if vv 0 = c then δ else 0) - (if vv k = c then δ else 0) := by
      intro k
      induction k with
      | zero => rw [Finset.sum_range_zero, sub_self]
      | succ k ih => rw [Finset.sum_range_succ, ih]; ring
    exact htel n
  have hΔ_le : ∀ a b, Δ a b ≤ (n : ℝ) * δ := by
    intro a b
    simp only [hΔ]
    calc ∑ i ∈ Finset.range n, d i a b
      ≤ ∑ i ∈ Finset.range n, (if vv i = a ∧ vv (i + 1) = b ∧ f (vv i) (vv (i + 1)) < cap (vv i)
        (vv (i + 1)) then δ else (0 : ℝ)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [hd_ind i a b]
        have hY : (0 : ℝ) ≤ (if vv i = b ∧ vv (i + 1) = a ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i)
          (vv (i + 1)) then δ else 0) := by
          by_cases hC : (vv i = b ∧ vv (i + 1) = a ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i)
            (vv (i + 1)))
          · rw [ite_eq_left hC]; exact le_of_lt hδ_pos
          · rw [ite_eq_right hC]
        linarith
      _ ≤ ∑ _ ∈ Finset.range n, δ := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hC : (vv i = a ∧ vv (i + 1) = b ∧ f (vv i) (vv (i + 1)) < cap (vv i)
          (vv (i + 1)))
        · rw [ite_eq_left hC]
        · rw [ite_eq_right hC]; exact le_of_lt hδ_pos
      _ = (n : ℝ) * δ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hΔ_ge : ∀ a b, -((n : ℝ) * δ) ≤ Δ a b := by
    intro a b
    simp only [hΔ]
    calc -((n : ℝ) * δ) = ∑ _ ∈ Finset.range n, (-δ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ Finset.range n, d i a b := by
        apply Finset.sum_le_sum
        intro i _
        rw [hd_ind i a b]
        have hX0 : (0 : ℝ) ≤ (if vv i = a ∧ vv (i + 1) = b ∧ f (vv i) (vv (i + 1)) < cap (vv i)
          (vv (i + 1)) then δ else 0) := by
          by_cases hC : (vv i = a ∧ vv (i + 1) = b ∧ f (vv i) (vv (i + 1)) < cap (vv i)
            (vv (i + 1)))
          · rw [ite_eq_left hC]; exact le_of_lt hδ_pos
          · rw [ite_eq_right hC]
        have hY1 : (if vv i = b ∧ vv (i + 1) = a ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i)
          (vv (i + 1)) then δ else 0) ≤ δ := by
          by_cases hC : (vv i = b ∧ vv (i + 1) = a ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i)
            (vv (i + 1)))
          · rw [ite_eq_left hC]
          · rw [ite_eq_right hC]; exact le_of_lt hδ_pos
        linarith
  have hle' : ∀ a b, f' a b ≤ cap a b := by
    intro a b
    by_cases hF : ∃ i, i ∈ Finset.range n ∧ vv i = a ∧ vv (i + 1) = b ∧ f (vv i) (vv (i + 1)) < cap
      (vv i) (vv (i + 1))
    · obtain ⟨i, hi, ha, hb, hlt⟩ := hF
      have hgi : gap i = cap a b - f a b := by
        simp only [hgap]
        rw [ite_eq_left hlt, ha, hb]
      have hmi : m ≤ cap a b - f a b := by
        have h1 : m ≤ gap i := by
          rw [hm]; exact Finset.min'_le _ _ (Finset.mem_image_of_mem gap hi)
        rwa [hgi] at h1
      have h2 : Δ a b ≤ cap a b - f a b := le_trans (hΔ_le a b) (by linarith [hnnδ, hmi])
      simp only [hf']
      linarith [h2]
    · have hni : ∀ i ∈ Finset.range n,
      ¬(vv i = a ∧ vv (i + 1) = b ∧ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))) := by
      intro i hi hcon
      exact hF ⟨i, hi, hcon.1, hcon.2.1, hcon.2.2⟩
      have h1 : ∀ i ∈ Finset.range n, d i a b ≤ 0 := by
        intro i hi
        rw [hd_ind i a b, ite_eq_right (hni i hi), zero_sub]
        have hY : (0 : ℝ) ≤ (if vv i = b ∧ vv (i + 1) = a ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i)
          (vv (i + 1)) then δ else 0) := by
          by_cases hC : (vv i = b ∧ vv (i + 1) = a ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i)
            (vv (i + 1)))
          · rw [ite_eq_left hC]; exact le_of_lt hδ_pos
          · rw [ite_eq_right hC]
        exact neg_nonpos.mpr hY
      have h2 : Δ a b ≤ 0 := by
        simp only [hΔ]
        calc ∑ i ∈ Finset.range n, d i a b ≤ ∑ _ ∈ Finset.range n, (0 : ℝ) := Finset.sum_le_sum h1
          _ = 0 := by simp
      simp only [hf']
      have h3 := hle a b
      linarith [h2, h3]
  have h0' : ∀ a b, 0 ≤ f' a b := by
    intro a b
    by_cases hB : ∃ i, i ∈ Finset.range n ∧ vv i = b ∧ vv (i + 1) = a ∧ ¬ f (vv i) (vv (i + 1)) <
      cap (vv i) (vv (i + 1))
    · obtain ⟨i, hi, ha, hb, hnge⟩ := hB
      have hgi : gap i = f a b := by
        simp only [hgap]
        rw [ite_eq_right hnge, ha, hb]
      have hmi : m ≤ f a b := by
        have h1 : m ≤ gap i := by
          rw [hm]; exact Finset.min'_le _ _ (Finset.mem_image_of_mem gap hi)
        rwa [hgi] at h1
      have h2 : -(f a b) ≤ Δ a b := by
        have h3 := hΔ_ge a b
        linarith [hnnδ, hmi]
      simp only [hf']
      have h3 := h0 a b
      linarith [h2, h3]
    · have hni : ∀ i ∈ Finset.range n,
      ¬(vv i = b ∧ vv (i + 1) = a ∧ ¬ f (vv i) (vv (i + 1)) < cap (vv i) (vv (i + 1))) := by
      intro i hi hcon
      exact hB ⟨i, hi, hcon.1, hcon.2.1, hcon.2.2⟩
      have h1 : ∀ i ∈ Finset.range n, 0 ≤ d i a b := by
        intro i hi
        rw [hd_ind i a b, ite_eq_right (hni i hi), sub_zero]
        have hX : (0 : ℝ) ≤ (if vv i = a ∧ vv (i + 1) = b ∧ f (vv i) (vv (i + 1)) < cap (vv i)
          (vv (i + 1)) then δ else 0) := by
          by_cases hC : (vv i = a ∧ vv (i + 1) = b ∧ f (vv i) (vv (i + 1)) < cap (vv i)
            (vv (i + 1)))
          · rw [ite_eq_left hC]; exact le_of_lt hδ_pos
          · rw [ite_eq_right hC]
        exact hX
      have h2 : 0 ≤ Δ a b := by
        simp only [hΔ]; exact Finset.sum_nonneg h1
      simp only [hf']
      have h3 := h0 a b
      linarith [h2, h3]
  have hcons' : ∀ a, a ≠ s → a ≠ t → (∑ u, f' u a) = ∑ w, f' a w := by
    intro a has hat
    have hbal_a := hbal a
    have hif0 : (if vv 0 = a then δ else (0 : ℝ)) = 0 := by
      rw [hstart]
      exact ite_eq_right (fun h => has h.symm)
    have hifn : (if vv n = a then δ else (0 : ℝ)) = 0 := by
      rw [hend]
      exact ite_eq_right (fun h => hat h.symm)
    rw [hif0, hifn, sub_zero] at hbal_a
    have heq : (∑ u, Δ u a) = (∑ b, Δ a b) := by linarith [hbal_a]
    have hca := hcons a has hat
    simp only [hf', Finset.sum_add_distrib]
    linarith [heq, hca]
  have hval : flowValue s f < flowValue s f' := by
    have hbal_s := hbal s
    have hif0 : (if vv 0 = s then δ else (0 : ℝ)) = δ := by
      rw [hstart]
      exact ite_eq_left rfl
    have hifn : (if vv n = s then δ else (0 : ℝ)) = 0 := by
      rw [hend]
      exact ite_eq_right (fun h => hst h.symm)
    rw [hif0, hifn, sub_zero] at hbal_s
    unfold flowValue
    simp only [hf', Finset.sum_add_distrib]
    linarith [hbal_s, hδ_pos]
  exact ⟨f', ⟨h0', hle', hcons'⟩, hval⟩

end MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

namespace MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/--
[max_flow_min_cut](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MaxFlowMinCut.lean)
-/
@[path]
lemma max_flow_min_cut
  [Fintype V] [DecidableEq V]
  {cap : V → V → ℝ}
  {s t : V}
-- given
  (hcap : ∀ u v, 0 ≤ cap u v)
  (hst : s ≠ t) :
-- imply
  ∃ f : V → V → ℝ, IsFeasibleFlow cap s t f ∧
    (∀ f' : V → V → ℝ, IsFeasibleFlow cap s t f' → flowValue s f' ≤ flowValue s f) ∧
    (∀ S : Finset V, IsSTCut s t S → flowValue s f ≤ cutCapacity cap S) ∧
    ∃ S : Finset V, IsSTCut s t S ∧ flowValue s f = cutCapacity cap S := by
-- proof
  obtain ⟨f, hf, hmax⟩ := exists_max_flow cap hcap s t
  have ⟨h0, hle, hcons⟩ := hf
  classical
  set S : Finset V := Finset.univ.filter (ReachableFrom cap s f) with hS
  have hsS : s ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨0, fun _ => s, rfl, fun i hi => absurd hi (by omega), rfl⟩
  have htS : t ∉ S := by
    intro ht
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    obtain ⟨k, w, h0w, hstepw, hkw⟩ := ht
    obtain ⟨f', hff', hlt⟩ := exists_augmenting_flow cap s t hst f hf k w h0w hstepw hkw
    exact (not_lt.mpr (hmax f' hff')) hlt
  have hsat : ∀ u ∈ S, ∀ w ∈ Finset.univ \ S, f u w = cap u w ∧ f w u = 0 := by
    intro u hu w hw
    have huR : ReachableFrom cap s f u := by
      simpa only [hS, Finset.mem_filter, Finset.mem_univ, true_and] using hu
    have hne : u ≠ w := by
      intro heq
      rw [← heq] at hw
      exact (Finset.mem_sdiff.mp hw).2 hu
    constructor
    · by_contra hcon
      have hlt : f u w < cap u w := lt_of_le_of_ne (hle u w) hcon
      have hRw : ReachableFrom cap s f w := reachable_extend cap s f u w huR (Or.inl hlt)
      have hmem : w ∈ S := by
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hRw
      exact (Finset.mem_sdiff.mp hw).2 hmem
    · by_contra hcon
      have hpos : 0 < f w u := lt_of_le_of_ne' (h0 w u) hcon
      have hRw : ReachableFrom cap s f w := reachable_extend cap s f u w huR (Or.inr hpos)
      have hmem : w ∈ S := by
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hRw
      exact (Finset.mem_sdiff.mp hw).2 hmem
  have heq : flowValue s f = cutCapacity cap S := by
    have hcf := cutFlow_eq s t f hf.2.2 S hsS htS
    rw [hcf]
    unfold cutCapacity
    have hfwd : (∑ u ∈ S, ∑ v ∈ Finset.univ \ S, f u v) =
      ∑ u ∈ S, ∑ v ∈ Finset.univ \ S, cap u v := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro w hw
      exact (hsat u hu w hw).1
    have hbwd : (∑ u ∈ S, ∑ v ∈ Finset.univ \ S, f v u) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      apply Finset.sum_eq_zero
      intro w hw
      exact (hsat u hu w hw).2
    rw [hfwd, hbwd, sub_zero]
  exact ⟨f, hf, hmax, fun S' hS' => flowValue_le_cutCapacity cap s t f hf S' hS', S, ⟨hsS, htS⟩,
    heq⟩

end MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted


-- created on 2026-10-20
-- updated on 2026-10-26
