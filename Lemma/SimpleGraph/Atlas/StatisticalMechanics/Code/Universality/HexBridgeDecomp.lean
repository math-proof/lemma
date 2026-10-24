import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexBridgeDecomp
open StatMech StatMech.Universality StatMech.Universality.HexBridge


/--
[rungs_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma rungs_ne_nil_eq
  {b : HexBridge} :
-- imply
  b.rungs ≠ [] := by
-- proof
  apply StatMech.Universality.HexBridge.rungs_ne_nil b

/--
[mem_rungs_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma mem_rungs_fst_eq
  {b : HexBridge}
  {p : ℕ × ℤ}
-- given
  (hp : p ∈ b.rungs) :
-- imply
  p.1 = b.width := by
-- proof
  apply StatMech.Universality.HexBridge.mem_rungs_fst hp

/--
[length_rungs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma length_rungs_eq
  {b : HexBridge} :
-- imply
  b.rungs.length = b.content.length := by
-- proof
  apply StatMech.Universality.HexBridge.length_rungs b

/--
[strictDecreasingWidths_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma strictDecreasingWidths_nil_eq :
-- imply
  StrictDecreasingWidths [] := by
-- proof
  apply StatMech.Universality.strictDecreasingWidths_nil

/--
[strictDecreasingWidths_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma strictDecreasingWidths_cons_eq
  {b : HexBridge}
  {bs : List HexBridge} :
-- imply
  StrictDecreasingWidths (b :: bs) ↔ (∀ c ∈ bs, b.width > c.width) ∧ StrictDecreasingWidths bs := by
-- proof
  apply StatMech.Universality.strictDecreasingWidths_cons

/--
[StrictDecreasingWidths.tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma tail_eq
  {b : HexBridge}
  {bs : List HexBridge}
-- given
  (h : StrictDecreasingWidths (b :: bs)) :
-- imply
  StrictDecreasingWidths bs := by
-- proof
  apply StatMech.Universality.StrictDecreasingWidths.tail h

/--
[StrictDecreasingWidths.head_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma head_gt_eq
  {b : HexBridge}
  {bs : List HexBridge}
  {c : HexBridge}
-- given
  (h : StrictDecreasingWidths (b :: bs))
  (hc : c ∈ bs) :
-- imply
  b.width > c.width := by
-- proof
  apply StatMech.Universality.StrictDecreasingWidths.head_gt h hc

/--
[bridgeRecompose_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma bridgeRecompose_nil_eq :
-- imply
  bridgeRecompose [] = [] := by
-- proof
  apply StatMech.Universality.bridgeRecompose_nil

/--
[bridgeRecompose_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma bridgeRecompose_cons_eq
  {b : HexBridge}
  {bs : List HexBridge} :
-- imply
  bridgeRecompose (b :: bs) = b.rungs ++ bridgeRecompose bs := by
-- proof
  apply StatMech.Universality.bridgeRecompose_cons b bs

/--
[bridgeRecompose_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma bridgeRecompose_append_eq
  {bs cs : List HexBridge} :
-- imply
  bridgeRecompose (bs ++ cs) = bridgeRecompose bs ++ bridgeRecompose cs := by
-- proof
  apply StatMech.Universality.bridgeRecompose_append bs cs

/--
[mem_bridgeRecompose_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma mem_bridgeRecompose_fst_eq
  {bs : List HexBridge}
  {p : ℕ × ℤ}
-- given
  (hp : p ∈ bridgeRecompose bs) :
-- imply
  ∃ b ∈ bs, p.1 = b.width := by
-- proof
  apply StatMech.Universality.mem_bridgeRecompose_fst hp

/--
[hexHW_lead_drop_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_lead_drop_append_eq
  {p : ℕ × ℤ}
  {rest : List (ℕ × ℤ)} :
-- imply
  hexHW_leadRun p rest ++ hexHW_dropRun p rest = p :: rest := by
-- proof
  apply StatMech.Universality.hexHW_lead_drop_append p rest

/--
[hexHW_dropRun_length_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_dropRun_length_lt_eq
  {p : ℕ × ℤ}
  {rest : List (ℕ × ℤ)} :
-- imply
  (hexHW_dropRun p rest).length < (p :: rest).length := by
-- proof
  apply StatMech.Universality.hexHW_dropRun_length_lt p rest

/--
[hexHW_leadRun_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_leadRun_ne_nil_eq
  {p : ℕ × ℤ}
  {rest : List (ℕ × ℤ)} :
-- imply
  hexHW_leadRun p rest ≠ [] := by
-- proof
  apply StatMech.Universality.hexHW_leadRun_ne_nil p rest

/--
[hexHW_leadRun_content_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_leadRun_content_ne_eq
  {p : ℕ × ℤ}
  {rest : List (ℕ × ℤ)} :
-- imply
  (hexHW_leadRun p rest).map Prod.snd ≠ [] := by
-- proof
  apply StatMech.Universality.hexHW_leadRun_content_ne p rest

/--
[hexHW_dropRun_sublist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_dropRun_sublist_eq
  {p : ℕ × ℤ}
  {rest : List (ℕ × ℤ)} :
-- imply
  hexHW_dropRun p rest <+ p :: rest := by
-- proof
  apply StatMech.Universality.hexHW_dropRun_sublist p rest

/--
[hexHW_leadRun_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_leadRun_fst_eq
  {p : ℕ × ℤ}
  {rest : List (ℕ × ℤ)}
  {q : ℕ × ℤ}
-- given
  (hq : q ∈ hexHW_leadRun p rest) :
-- imply
  q.1 = p.1 := by
-- proof
  apply StatMech.Universality.hexHW_leadRun_fst p rest hq

/--
[hexHW_WF_dropRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_WF_dropRun_eq
  {p : ℕ × ℤ}
  {rest : List (ℕ × ℤ)}
-- given
  (h : hexHW_WF (p :: rest)) :
-- imply
  hexHW_WF (hexHW_dropRun p rest) := by
-- proof
  apply StatMech.Universality.hexHW_WF_dropRun p rest h

/--
[bridgeDecomp_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma bridgeDecomp_nil_eq
-- given
  (h : hexHW_WF []) :
-- imply
  bridgeDecomp [] h = [] := by
-- proof
  apply StatMech.Universality.bridgeDecomp_nil h

/--
[bridgeDecomp_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma bridgeDecomp_cons_eq
  {p : ℕ × ℤ}
  {rest : List (ℕ × ℤ)}
-- given
  (h : hexHW_WF (p :: rest)) :
-- imply
  bridgeDecomp (p :: rest) h = (⟨p.1, h p List.mem_cons_self, (hexHW_leadRun p rest).map Prod.snd, hexHW_leadRun_content_ne p rest⟩ : HexBridge) :: bridgeDecomp (hexHW_dropRun p rest) (hexHW_WF_dropRun p rest h) := by
-- proof
  apply StatMech.Universality.bridgeDecomp_cons p rest h

/--
[bridgeDecomp_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma bridgeDecomp_congr_eq
  {γ γ' : List (ℕ × ℤ)}
-- given
  (h : hexHW_WF γ)
  (h' : hexHW_WF γ')
  (he : γ = γ') :
-- imply
  bridgeDecomp γ h = bridgeDecomp γ' h' := by
-- proof
  apply StatMech.Universality.bridgeDecomp_congr γ γ' h h' he

/--
[HexBridge.eq_of](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma eq_of_eq
  {b c : HexBridge}
-- given
  (hw : b.width = c.width)
  (hc : b.content = c.content) :
-- imply
  b = c := by
-- proof
  apply StatMech.Universality.HexBridge.eq_of hw hc

/--
[HexBridge.eq_of_rungs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma eq_of_rungs_eq
  {b c : HexBridge}
-- given
  (h : b.rungs = c.rungs) :
-- imply
  b = c := by
-- proof
  apply StatMech.Universality.HexBridge.eq_of_rungs h

/--
[hexHW_wf_bridgeRecompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_wf_bridgeRecompose_eq
  {bs : List HexBridge} :
-- imply
  hexHW_WF (bridgeRecompose bs) := by
-- proof
  apply StatMech.Universality.hexHW_wf_bridgeRecompose bs

/--
[hexHW_recompose_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_recompose_decomp_eq :
-- imply
  ∀ (γ : List (ℕ × ℤ)) (h : hexHW_WF γ), bridgeRecompose (bridgeDecomp γ h) = γ := by
-- proof
  apply StatMech.Universality.hexHW_recompose_decomp

/--
[hexHW_takeWhile_recompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_takeWhile_recompose_eq
  {b : HexBridge}
  {bs : List HexBridge}
-- given
  (h : StrictDecreasingWidths (b :: bs)) :
-- imply
  (bridgeRecompose (b :: bs)).takeWhile (fun q => q.1 == b.width) = b.rungs := by
-- proof
  apply StatMech.Universality.hexHW_takeWhile_recompose b bs h

/--
[hexHW_dropWhile_recompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_dropWhile_recompose_eq
  {b : HexBridge}
  {bs : List HexBridge}
-- given
  (h : StrictDecreasingWidths (b :: bs)) :
-- imply
  (bridgeRecompose (b :: bs)).dropWhile (fun q => q.1 == b.width) = bridgeRecompose bs := by
-- proof
  apply StatMech.Universality.hexHW_dropWhile_recompose b bs h

/--
[hexHW_decomp_recompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_decomp_recompose_eq :
-- imply
  ∀ (bs : List HexBridge) (h : hexHW_WF (bridgeRecompose bs)), StrictDecreasingWidths bs → bridgeDecomp (bridgeRecompose bs) h = bs := by
-- proof
  apply StatMech.Universality.hexHW_decomp_recompose

/--
[hexHW_bridgeRecompose_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_bridgeRecompose_injOn_eq
  {bs cs : List HexBridge}
-- given
  (hb : StrictDecreasingWidths bs)
  (hc : StrictDecreasingWidths cs)
  (heq : bridgeRecompose bs = bridgeRecompose cs) :
-- imply
  bs = cs := by
-- proof
  apply StatMech.Universality.hexHW_bridgeRecompose_injOn hb hc heq

/--
[hexHW_bridge_decomp_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_bridge_decomp_apply_eq
  {bs : {bs : List HexBridge // StrictDecreasingWidths bs}} :
-- imply
  (hexHW_bridge_decomp bs : List (ℕ × ℤ)) = bridgeRecompose bs.1 := by
-- proof
  apply StatMech.Universality.hexHW_bridge_decomp_apply bs

/--
[hexHW_bridge_decomp_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_bridge_decomp_symm_apply_eq
  {γ : {γ : List (ℕ × ℤ) // hexHW_IsValidWalk γ}} :
-- imply
  ((hexHW_bridge_decomp.symm γ : {bs : List HexBridge // StrictDecreasingWidths bs}) : List HexBridge) = bridgeDecomp γ.1 (by obtain ⟨bs, _, hrec⟩ := γ.2 rw [← hrec]; exact hexHW_wf_bridgeRecompose bs) := by
-- proof
  apply StatMech.Universality.hexHW_bridge_decomp_symm_apply γ

/--
[hexHW_decomp_strictDecreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_decomp_strictDecreasing_eq
  {γ : List (ℕ × ℤ)}
-- given
  (h : hexHW_WF γ)
  (hv : hexHW_IsValidWalk γ) :
-- imply
  StrictDecreasingWidths (bridgeDecomp γ h) := by
-- proof
  apply StatMech.Universality.hexHW_decomp_strictDecreasing γ h hv

/--
[hexHW_image_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_image_iff_eq
  {bs : List HexBridge} :
-- imply
  (∃ (γ : List (ℕ × ℤ)) (h : hexHW_WF γ), hexHW_IsValidWalk γ ∧ bridgeDecomp γ h = bs) ↔ StrictDecreasingWidths bs := by
-- proof
  apply StatMech.Universality.hexHW_image_iff bs

/--
[hexHW_strictIncreasing_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_strictIncreasing_reverse_eq
  {bs : List HexBridge} :
-- imply
  StrictIncreasingWidths bs ↔ StrictDecreasingWidths bs.reverse := by
-- proof
  apply StatMech.Universality.hexHW_strictIncreasing_reverse bs


-- created on 2026-10-23
