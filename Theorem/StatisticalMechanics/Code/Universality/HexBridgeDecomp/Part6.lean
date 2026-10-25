/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part6


namespace StatMech.Universality

open List


@[simp]
theorem bridgeDecomp_nil (h : hexHW_WF []) : bridgeDecomp [] h = [] := by rw [bridgeDecomp]

theorem bridgeDecomp_cons (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) (h : hexHW_WF (p :: rest)) :
    bridgeDecomp (p :: rest) h =
      (⟨p.1, h p List.mem_cons_self, (hexHW_leadRun p rest).map Prod.snd,
          hexHW_leadRun_content_ne p rest⟩ : HexBridge)
        :: bridgeDecomp (hexHW_dropRun p rest) (hexHW_WF_dropRun p rest h) := by
  rw [bridgeDecomp]


theorem bridgeDecomp_congr (γ γ' : List (ℕ × ℤ)) (h : hexHW_WF γ) (h' : hexHW_WF γ')
    (he : γ = γ') : bridgeDecomp γ h = bridgeDecomp γ' h' := by
  subst he; rfl


theorem HexBridge.eq_of {b c : HexBridge} (hw : b.width = c.width)
    (hc : b.content = c.content) : b = c := by
  cases b; cases c; simp_all


theorem HexBridge.eq_of_rungs {b c : HexBridge} (h : b.rungs = c.rungs) : b = c := by
  have hwb : b.width = c.width := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ b.rungs_ne_nil
    have hpc : p ∈ c.rungs := h ▸ hp
    rw [← HexBridge.mem_rungs_fst hp, ← HexBridge.mem_rungs_fst hpc]
  have hcontent : b.content = c.content := by
    have : b.rungs.map Prod.snd = c.rungs.map Prod.snd := by rw [h]
    simpa [HexBridge.rungs, List.map_map, Function.comp] using this
  exact HexBridge.eq_of hwb hcontent


theorem hexHW_wf_bridgeRecompose (bs : List HexBridge) : hexHW_WF (bridgeRecompose bs) := by
  intro q hq
  obtain ⟨b, _, hqb⟩ := mem_bridgeRecompose_fst hq
  rw [hqb]; exact b.width_pos


theorem hexHW_recompose_decomp : ∀ (γ : List (ℕ × ℤ)) (h : hexHW_WF γ),
    bridgeRecompose (bridgeDecomp γ h) = γ
  | [], h => by rw [bridgeDecomp_nil]; rfl
  | p :: rest, h => by
    rw [bridgeDecomp_cons, bridgeRecompose_cons]
    
    have hbr : (HexBridge.mk p.1 (h p List.mem_cons_self)
        ((hexHW_leadRun p rest).map Prod.snd) (hexHW_leadRun_content_ne p rest)).rungs
          = hexHW_leadRun p rest := by
      simp only [HexBridge.rungs, List.map_map]
      conv_rhs => rw [← List.map_id (hexHW_leadRun p rest)]
      apply List.map_congr_left
      intro q hq
      ext
      · exact (hexHW_leadRun_fst p rest hq).symm
      · rfl
    rw [hbr]
    rw [hexHW_recompose_decomp (hexHW_dropRun p rest) (hexHW_WF_dropRun p rest h)]
    exact hexHW_lead_drop_append p rest
  termination_by γ _ => γ.length
  decreasing_by exact hexHW_dropRun_length_lt p rest


theorem hexHW_takeWhile_recompose (b : HexBridge) (bs : List HexBridge)
    (h : StrictDecreasingWidths (b :: bs)) :
    (bridgeRecompose (b :: bs)).takeWhile (fun q => q.1 == b.width) = b.rungs := by
  rw [bridgeRecompose_cons]
  have hb : ∀ a ∈ b.rungs, (a.1 == b.width) = true :=
    fun a ha => by simp [HexBridge.mem_rungs_fst ha]
  rw [List.takeWhile_append_of_pos hb]
  have htail : (bridgeRecompose bs).takeWhile (fun q => q.1 == b.width) = [] := by
    cases hbs : bridgeRecompose bs with
    | nil => simp
    | cons p rest =>
      rw [List.takeWhile_cons]
      obtain ⟨c, hc, hpc⟩ := mem_bridgeRecompose_fst
        (by rw [hbs]; exact List.mem_cons_self : p ∈ bridgeRecompose bs)
      have hlt : c.width < b.width := h.head_gt hc
      rw [if_neg (by simp; rw [hpc]; omega)]
  rw [htail, List.append_nil]


theorem hexHW_dropWhile_recompose (b : HexBridge) (bs : List HexBridge)
    (h : StrictDecreasingWidths (b :: bs)) :
    (bridgeRecompose (b :: bs)).dropWhile (fun q => q.1 == b.width) = bridgeRecompose bs := by
  rw [bridgeRecompose_cons]
  have hb : ∀ a ∈ b.rungs, (a.1 == b.width) = true :=
    fun a ha => by simp [HexBridge.mem_rungs_fst ha]
  rw [List.dropWhile_append_of_pos hb]
  cases hbs : bridgeRecompose bs with
  | nil => simp
  | cons p rest =>
    rw [List.dropWhile_cons]
    obtain ⟨c, hc, hpc⟩ := mem_bridgeRecompose_fst
      (by rw [hbs]; exact List.mem_cons_self : p ∈ bridgeRecompose bs)
    have hlt : c.width < b.width := h.head_gt hc
    rw [if_neg (by simp; rw [hpc]; omega)]


theorem hexHW_decomp_recompose : ∀ (bs : List HexBridge) (h : hexHW_WF (bridgeRecompose bs)),
    StrictDecreasingWidths bs → bridgeDecomp (bridgeRecompose bs) h = bs := by
  intro bs
  induction bs with
  | nil => intro h _; exact bridgeDecomp_nil h
  | cons b bs ih =>
    intro h hsdw
    obtain ⟨p0, rs, hpr0⟩ := List.exists_cons_of_ne_nil b.rungs_ne_nil
    have hrec_eq : bridgeRecompose (b :: bs) = p0 :: (rs ++ bridgeRecompose bs) := by
      rw [bridgeRecompose_cons, hpr0, List.cons_append]
    have hp01 : p0.1 = b.width := by
      apply HexBridge.mem_rungs_fst; rw [hpr0]; exact List.mem_cons_self
    rw [bridgeDecomp_congr _ _ h (hrec_eq ▸ h) hrec_eq, bridgeDecomp_cons]
    have hlead_eq : hexHW_leadRun p0 (rs ++ bridgeRecompose bs) = b.rungs := by
      simp only [hexHW_leadRun]
      rw [← hrec_eq]
      rw [show (fun q : ℕ × ℤ => q.1 == p0.1) = (fun q => q.1 == b.width) from by rw [hp01]]
      exact hexHW_takeWhile_recompose b bs hsdw
    have hdrop_eq : hexHW_dropRun p0 (rs ++ bridgeRecompose bs) = bridgeRecompose bs := by
      simp only [hexHW_dropRun]
      rw [← hrec_eq]
      rw [show (fun q : ℕ × ℤ => q.1 == p0.1) = (fun q => q.1 == b.width) from by rw [hp01]]
      exact hexHW_dropWhile_recompose b bs hsdw
    have hp0pos : 0 < p0.1 := by rw [hp01]; exact b.width_pos
    have hbhead : (⟨p0.1, hp0pos, (hexHW_leadRun p0 (rs ++ bridgeRecompose bs)).map Prod.snd,
        hexHW_leadRun_content_ne p0 (rs ++ bridgeRecompose bs)⟩ : HexBridge) = b := by
      apply HexBridge.eq_of
      · exact hp01
      · show (hexHW_leadRun p0 (rs ++ bridgeRecompose bs)).map Prod.snd = b.content
        rw [hlead_eq]
        simp [HexBridge.rungs, List.map_map]
    rw [hbhead]
    congr 1
    rw [bridgeDecomp_congr _ (bridgeRecompose bs) _ (hexHW_wf_bridgeRecompose bs) hdrop_eq]
    exact ih (hexHW_wf_bridgeRecompose bs) hsdw.tail


theorem hexHW_bridgeRecompose_injOn {bs cs : List HexBridge}
    (hb : StrictDecreasingWidths bs) (hc : StrictDecreasingWidths cs)
    (heq : bridgeRecompose bs = bridgeRecompose cs) : bs = cs := by
  have e1 : bridgeDecomp (bridgeRecompose bs) (hexHW_wf_bridgeRecompose bs) = bs :=
    hexHW_decomp_recompose bs _ hb
  have e2 : bridgeDecomp (bridgeRecompose cs) (hexHW_wf_bridgeRecompose cs) = cs :=
    hexHW_decomp_recompose cs _ hc
  rw [← e1, ← e2]
  exact bridgeDecomp_congr _ _ _ _ heq


end StatMech.Universality
