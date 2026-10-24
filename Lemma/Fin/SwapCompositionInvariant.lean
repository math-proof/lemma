import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.GeometricAlgebra.OppositeConjugacyComposition
open GeometricAlgebra


/--
[swap_composition_base](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyComposition.lean)
-/
@[path]
private lemma main
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {F F'₁ F'₂ : Flag k V}
-- given
  (h₁ : Flag.isOppositeFlag F F'₁)
  (h₂ : Flag.isOppositeFlag F F'₂) :
-- imply
  SwapCompositionInvariant F F'₁ F'₂ h₁ h₂ (LinearEquiv.refl k V) 0 where preserves_F :=
-- proof
  fun i => by simp [Submodule.map_id]
    maps_F'_done := fun j => by intro hge; omega



/--
[invariant_at_level](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyComposition.lean)
-/
private lemma invariant_at_level
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {step_hyp : SwapCompositionStepHyp k V}
  {F F'₁ F'₂ : Flag k V}
  {m : ℕ}
-- given
  (h₁ : Flag.isOppositeFlag F F'₁)
  (h₂ : Flag.isOppositeFlag F F'₂)
  (hm : m ≤ F'₁.len) :
-- imply
  ∃ e : V ≃ₗ[k] V, SwapCompositionInvariant F F'₁ F'₂ h₁ h₂ e m := by
-- proof
  induction m with
  | zero => exact ⟨LinearEquiv.refl k V, swap_composition_base F F'₁ F'₂ h₁ h₂⟩
  | succ m ih =>
    obtain ⟨e_prev, inv⟩ := ih (Nat.le_of_succ_le hm)
    exact step_hyp.step F F'₁ F'₂ h₁ h₂ m (Nat.lt_of_succ_le hm) e_prev inv



/--
[opposite_conjugacy_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyComposition.lean)
-/
private lemma opposite_conjugacy_of_step
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {step_hyp : SwapCompositionStepHyp k V} :
-- imply
  OppositeConjugacyCompositionHyp k V where compose_swaps :=
-- proof
  fun F F'₁ F'₂ h₁ h₂ => by
    obtain ⟨e, inv⟩ := invariant_at_level step_hyp F F'₁ F'₂ h₁ h₂ F'₁.len le_rfl
    have hlen : F'₁.len = F'₂.len := opposite_flags_same_len F F'₁ F'₂ h₁ h₂
    refine ⟨e, hlen, inv.preserves_F, fun i => ?_⟩
    have hmapped := inv.maps_F'_done i (by omega)
    convert hmapped using 2



/--
[complIsomOfIsCompl_coe_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyComposition.lean)
-/
private lemma complIsomOfIsCompl_coe_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {W C₁ C₂ : Submodule k V}
  {c : C₁}
-- given
  (hc₁ : IsCompl W C₁)
  (hc₂ : IsCompl W C₂) :
-- imply
  (complIsomOfIsCompl W C₁ C₂ hc₁ hc₂ c : V) = (Submodule.linearProjOfIsCompl C₂ W hc₂.symm (c : V) : V) := by
-- proof
  simp only [complIsomOfIsCompl]
  rw [LinearEquiv.ofBijective_apply]
  rfl



/--
[swapComplement_sub_mem_W](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyComposition.lean)
-/
private lemma swapComplement_sub_mem_W
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {W C₁ C₂ : Submodule k V}
  {v : V}
-- given
  (hc₁ : IsCompl W C₁)
  (hc₂ : IsCompl W C₂) :
-- imply
  swapComplement W C₁ C₂ hc₁ hc₂ v - v ∈ W := by
-- proof
  set e := swapComplement W C₁ C₂ hc₁ hc₂
  set decomp := Submodule.prodEquivOfIsCompl W C₁ hc₁
  set p := decomp.symm v
  have hv_eq : (p.1 : V) + (p.2 : V) = v := by
    have := decomp.apply_symm_apply v
    rw [Submodule.coe_prodEquivOfIsCompl' W C₁ hc₁] at this; exact this
  have he_v : e v = (p.1 : V) + e (p.2 : V) := by
    conv_lhs => rw [← hv_eq]
    rw [map_add, swapComplement_fix_W W C₁ C₂ hc₁ hc₂ _ p.1.property]
  rw [he_v, ← hv_eq]
  have : (p.1 : V) + e (p.2 : V) - ((p.1 : V) + (p.2 : V)) = e (p.2 : V) - (p.2 : V) := by abel
  rw [this]
  show (swapComplement W C₁ C₂ hc₁ hc₂) (p.2 : V) - (p.2 : V) ∈ W
  simp only [swapComplement, LinearEquiv.trans_apply]
  rw [Submodule.prodEquivOfIsCompl_symm_apply_right W C₁ hc₁ p.2]
  simp only [LinearEquiv.prodCongr_apply, map_zero]
  rw [Submodule.coe_prodEquivOfIsCompl' W C₂ hc₂]
  simp only [Submodule.coe_zero, zero_add]
  set φ_c := complIsomOfIsCompl W C₁ C₂ hc₁ hc₂ p.2
  set decomp₂ := Submodule.prodEquivOfIsCompl W C₂ hc₂
  set q := decomp₂.symm (p.2 : V)
  have hc_eq : (q.1 : V) + (q.2 : V) = (p.2 : V) := by
    have := decomp₂.apply_symm_apply (p.2 : V)
    rw [Submodule.coe_prodEquivOfIsCompl' W C₂ hc₂] at this; exact this
  have hφ_eq : (φ_c : V) = (q.2 : V) := by
    rw [complIsomOfIsCompl_coe_eq]
    show (↑((Submodule.linearProjOfIsCompl C₂ W hc₂.symm) ↑p.2) : V) = ↑q.2
    congr 1
    have := Submodule.prodEquivOfIsCompl_symm_apply hc₂ (↑p.2 : V)
    have hq_eq : q = (Submodule.linearProjOfIsCompl W C₂ hc₂ (↑p.2), Submodule.linearProjOfIsCompl C₂ W hc₂.symm (↑p.2)) := this
    rw [hq_eq]
  have hdiff : (φ_c : V) - (p.2 : V) = -(q.1 : V) := by
    rw [hφ_eq, ← hc_eq]; abel
  rw [hdiff]
  exact W.neg_mem q.1.property



/--
[swapComplement_preserves_of_both_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyComposition.lean)
-/
private lemma swapComplement_preserves_of_both_le
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {W C₁ C₂ S : Submodule k V}
-- given
  (hc₁ : IsCompl W C₁)
  (hc₂ : IsCompl W C₂)
  (hC₁_le : C₁ ≤ S)
  (hC₂_le : C₂ ≤ S) :
-- imply
  S.map (swapComplement W C₁ C₂ hc₁ hc₂).toLinearMap = S := by
-- proof
  apply map_eq_of_forall_mem
  · intro v hv
    set decomp := Submodule.prodEquivOfIsCompl W C₁ hc₁
    set p := decomp.symm v
    have hv_eq : (p.1 : V) + (p.2 : V) = v := by
      have := decomp.apply_symm_apply v
      rw [Submodule.coe_prodEquivOfIsCompl' W C₁ hc₁] at this; exact this
    have he_v : swapComplement W C₁ C₂ hc₁ hc₂ v =
      (p.1 : V) + swapComplement W C₁ C₂ hc₁ hc₂ (p.2 : V) := by
      conv_lhs => rw [← hv_eq]
      rw [map_add, swapComplement_fix_W W C₁ C₂ hc₁ hc₂ _ p.1.property]
    have hec₂ : swapComplement W C₁ C₂ hc₁ hc₂ (p.2 : V) ∈ C₂ := by
      have h2 := swapComplement_map_C W C₁ C₂ hc₁ hc₂
      rw [Submodule.ext_iff] at h2
      exact (h2 _).mp ⟨(p.2 : V), p.2.property, rfl⟩
    have hw_S : (p.1 : V) ∈ S := by
      have hc₁_S : (p.2 : V) ∈ S := hC₁_le p.2.property
      have : (p.1 : V) = v - (p.2 : V) := by rw [← hv_eq]; abel
      rw [this]; exact S.sub_mem hv hc₁_S
    rw [he_v]
    exact S.add_mem hw_S (hC₂_le hec₂)
  · intro v hv
    set e := swapComplement W C₁ C₂ hc₁ hc₂
    set decomp₂ := Submodule.prodEquivOfIsCompl W C₂ hc₂
    set q := decomp₂.symm v
    have hv_eq₂ : (q.1 : V) + (q.2 : V) = v := by
      have := decomp₂.apply_symm_apply v
      rw [Submodule.coe_prodEquivOfIsCompl' W C₂ hc₂] at this; exact this
    have he_symm_eq : e.symm v = (q.1 : V) + e.symm (q.2 : V) := by
      conv_lhs => rw [← hv_eq₂]
      rw [map_add]
      have : e.symm (q.1 : V) = (q.1 : V) := by
        rw [LinearEquiv.symm_apply_eq]
        exact (swapComplement_fix_W W C₁ C₂ hc₁ hc₂ _ q.1.property).symm
      rw [this]
    have he_symm_c₂ : e.symm (q.2 : V) ∈ C₁ := by
      have h_map := swapComplement_map_C W C₁ C₂ hc₁ hc₂
      rw [Submodule.ext_iff] at h_map
      obtain ⟨c₁, hc₁_mem, hc₁_eq⟩ := (h_map (q.2 : V)).mpr q.2.property
      have : e.symm (q.2 : V) = c₁ := by
        have h_eq : e c₁ = (q.2 : V) := hc₁_eq
        rw [← h_eq, LinearEquiv.symm_apply_apply]
      rw [this]; exact hc₁_mem
    have hw_mem : (q.1 : V) ∈ S := by
      have : (q.1 : V) = v - (q.2 : V) := by rw [← hv_eq₂]; abel
      rw [this]; exact S.sub_mem hv (hC₂_le q.2.property)
    rw [he_symm_eq]
    exact S.add_mem hw_mem (hC₁_le he_symm_c₂)



/--
[swapComplement_preserves_sup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyComposition.lean)
-/
private lemma swapComplement_preserves_sup
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {W C₁ C₂ S : Submodule k V}
-- given
  (hc₁ : IsCompl W C₁)
  (hc₂ : IsCompl W C₂)
  (hle : W ≤ S) :
-- imply
  S.map (swapComplement W C₁ C₂ hc₁ hc₂).toLinearMap = S := by
-- proof
  apply map_eq_of_forall_mem
  · intro v hv
    set e := swapComplement W C₁ C₂ hc₁ hc₂
    have hdiff : e v - v ∈ W := swapComplement_sub_mem_W W C₁ C₂ hc₁ hc₂ v
    have : e v = v + (e v - v) := by abel
    rw [this]; exact S.add_mem hv (hle hdiff)
  · intro v hv
    set e := swapComplement W C₁ C₂ hc₁ hc₂
    have hdiff : e.symm v - v ∈ W := by
      have h1 := swapComplement_sub_mem_W W C₁ C₂ hc₁ hc₂ (e.symm v)
      have h2 : e (e.symm v) = v := LinearEquiv.apply_symm_apply e v
      rw [h2] at h1
      have : e.symm v - v = -(v - e.symm v) := by abel
      rw [this]
      exact W.neg_mem h1
    have : e.symm v = v + (e.symm v - v) := by abel
    rw [this]; exact S.add_mem hv (hle hdiff)
set_option maxHeartbeats 800000 in



/--
[stepHyp_proof](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyComposition.lean)
-/
private lemma stepHyp_proof
  [Field k]
  [AddCommGroup V]
  [Module k V] :
-- imply
  SwapCompositionStepHyp k V where step :=
-- proof
  fun F F'₁ F'₂ h₁ h₂ levels_done h_lt e_prev inv => by
    have hFlen : F.len = F'₁.len := h₁.1
    have hlen₁₂ : F'₁.len = F'₂.len := opposite_flags_same_len F F'₁ F'₂ h₁ h₂
    set i_F : Fin F.len := ⟨levels_done, by omega⟩
    set target₁ : Fin F'₁.len := ⟨F'₁.len - 1 - levels_done, by omega⟩
    set target₂ : Fin F'₂.len := ⟨F'₂.len - 1 - levels_done, by omega⟩
    have hsup₁ := isOppositeFlag_sup_eq_top F F'₁ h₁ i_F
    have hinf₁ := isOppositeFlag_inf_eq_bot F F'₁ h₁ i_F
    have hsup₂ := isOppositeFlag_sup_eq_top F F'₂ h₂ i_F
    have hinf₂ := isOppositeFlag_inf_eq_bot F F'₂ h₂ i_F
    have hfin₁ : (⟨F'₁.len - 1 - i_F.val, by omega⟩ : Fin F'₁.len) = target₁ :=
      Fin.ext (by simp [i_F, target₁])
    have hfin₂ : (⟨F'₂.len - 1 - i_F.val, by omega⟩ : Fin F'₂.len) = target₂ :=
      Fin.ext (by simp [i_F, target₂])
    rw [hfin₁] at hsup₁ hinf₁
    rw [hfin₂] at hsup₂ hinf₂
    set C₁_trans := (F'₁.spaces target₁).map e_prev.toLinearMap
    have hc₁_trans : IsCompl (F.spaces i_F) C₁_trans := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x hx_F hx_C
        obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hx_C
        have h1 : e_prev.symm x ∈ F.spaces i_F := by
          have hpres := inv.preserves_F i_F
          have hx_map : x ∈ (F.spaces i_F).map e_prev.toLinearMap := by rwa [hpres]
          obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hx_map
          have : e_prev.symm x = z := by
            rw [← hzx]; exact LinearEquiv.symm_apply_apply e_prev z
          rw [this]; exact hz
        have h2 : e_prev.symm x ∈ F'₁.spaces target₁ := by
          have : e_prev.symm x = y := by
            rw [← hxy]; exact LinearEquiv.symm_apply_apply e_prev y
          rw [this]; exact hy
        have h3 : e_prev.symm x ∈ F.spaces i_F ⊓ F'₁.spaces target₁ :=
          Submodule.mem_inf.mpr ⟨h1, h2⟩
        rw [hinf₁, Submodule.mem_bot] at h3
        exact (LinearEquiv.map_eq_zero_iff e_prev.symm).mp h3
      · rw [codisjoint_iff, eq_top_iff]
        intro x _
        have : e_prev.symm x ∈ F.spaces i_F ⊔ F'₁.spaces target₁ := by
          rw [hsup₁]; trivial
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp this
        have hea : e_prev a ∈ F.spaces i_F := by
          have hpres := inv.preserves_F i_F
          rw [Submodule.ext_iff] at hpres
          exact (hpres (e_prev a)).mp ⟨a, ha, rfl⟩
        have heb : e_prev b ∈ C₁_trans := Submodule.mem_map.mpr ⟨b, hb, rfl⟩
        rw [show x = e_prev a + e_prev b from by
          rw [← map_add, hab, LinearEquiv.apply_symm_apply]]
        exact Submodule.mem_sup.mpr ⟨e_prev a, hea, e_prev b, heb, rfl⟩
    have hc₂ : IsCompl (F.spaces i_F) (F'₂.spaces target₂) :=
      IsCompl.mk (disjoint_iff.mpr hinf₂) (codisjoint_iff.mpr hsup₂)
    set adj := swapComplement (F.spaces i_F) C₁_trans (F'₂.spaces target₂) hc₁_trans hc₂
    set e_next := e_prev.trans adj
    refine ⟨e_next, ?_, ?_⟩
    ·
      intro m
      show (F.spaces m).map (e_prev.trans adj).toLinearMap = F.spaces m
      rw [LinearEquiv.coe_trans, Submodule.map_comp, inv.preserves_F m]
      by_cases hle : m.val ≤ levels_done
      · have hmle : F.spaces m ≤ F.spaces i_F := by
        obtain heq | hlt := eq_or_lt_of_le hle
        · exact (Fin.ext (by omega) : m = i_F) ▸ le_refl _
        · exact le_of_lt (F.strictMono (Fin.mk_lt_mk.mpr (by omega)))
        exact swapComplement_preserves_sub (F.spaces i_F) C₁_trans (F'₂.spaces target₂)
          (F.spaces m) hc₁_trans hc₂ hmle
      · push_neg at hle
        have hmge : F.spaces i_F ≤ F.spaces m :=
          le_of_lt (F.strictMono (Fin.mk_lt_mk.mpr (by omega)))
        exact swapComplement_preserves_sup (F.spaces i_F) C₁_trans (F'₂.spaces target₂)
          (F.spaces m) hc₁_trans hc₂ hmge
    ·
      intro j j₂ hj
      show (F'₁.spaces j).map (e_prev.trans adj).toLinearMap = F'₂.spaces j₂
      rw [LinearEquiv.coe_trans, Submodule.map_comp]
      by_cases hj_eq : j.val = target₁.val
      · have hj_fin : j = target₁ := Fin.ext hj_eq
        have hj₂_fin : j₂ = target₂ := by
          apply Fin.ext
          have ht₁ : target₁.val = F'₁.len - 1 - levels_done := rfl
          have ht₂ : target₂.val = F'₂.len - 1 - levels_done := rfl
          have hj₂_val : j₂.val = j.val := rfl
          omega
        rw [hj_fin, hj₂_fin]
        show C₁_trans.map adj.toLinearMap = F'₂.spaces target₂
        exact swapComplement_map_C (F.spaces i_F) C₁_trans (F'₂.spaces target₂) hc₁_trans hc₂
      · have hj_gt : j.val > target₁.val := by
        have : j.val ≥ F'₁.len - (levels_done + 1) := hj
        simp only [target₁] at *
        omega
        have hprev_mapped : (F'₁.spaces j).map e_prev.toLinearMap = F'₂.spaces j₂ := by
          have : j.val ≥ F'₁.len - levels_done := by
            simp only [target₁] at hj_gt
            omega
          exact inv.maps_F'_done j this
        rw [hprev_mapped]
        have hj₂_gt : j₂.val > target₂.val := by
          have ht₁ : target₁.val = F'₁.len - 1 - levels_done := rfl
          have ht₂ : target₂.val = F'₂.len - 1 - levels_done := rfl
          have hj₂_val : j₂.val = j.val := rfl
          omega
        have hC₂_le : F'₂.spaces target₂ ≤ F'₂.spaces j₂ :=
          le_of_lt (F'₂.strictMono (Fin.mk_lt_mk.mpr hj₂_gt))
        have hC₁_le : C₁_trans ≤ F'₂.spaces j₂ := by
          have h_mono : F'₁.spaces target₁ ≤ F'₁.spaces j :=
            le_of_lt (F'₁.strictMono (Fin.mk_lt_mk.mpr hj_gt))
          calc C₁_trans
            = (F'₁.spaces target₁).map e_prev.toLinearMap := rfl
            _ ≤ (F'₁.spaces j).map e_prev.toLinearMap := Submodule.map_mono h_mono
            _ = F'₂.spaces j₂ := hprev_mapped
        exact swapComplement_preserves_of_both_le (F.spaces i_F) C₁_trans
          (F'₂.spaces target₂) (F'₂.spaces j₂) hc₁_trans hc₂ hC₁_le hC₂_le



-- created on 2026-10-23
-- updated on 2026-10-24
