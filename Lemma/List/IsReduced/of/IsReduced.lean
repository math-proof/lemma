import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.ReflectionIdentificationGenuine
import Lemma.Nat.StrongExchangeForBruhat
import Lemma.List.IsReducedDrop.of.IsReduced
open CoxeterReflectionId


namespace StrongExchangeUnconditional

/--
[isReduced_of_append_isReduced](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/StrongExchangeUnconditional.lean)
-/
@[path]
lemma isReduced_of_append_isReduced
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {s : B}
-- given
  (h : cs.IsReduced (word ++ [s])) :
-- imply
  cs.IsReduced word := by
-- proof
  unfold CoxeterSystem.IsReduced at h ⊢
  have h1 := cs.length_wordProd_le word
  rw [List.length_append, List.length_singleton] at h
  have h3 : cs.wordProd (word ++ [s]) = cs.wordProd word * cs.simple s := by
    rw [cs.wordProd_append, cs.wordProd_singleton]
  rw [h3] at h
  obtain h4 | h4 <;> omega := cs.length_mul_simple (cs.wordProd word) s

end StrongExchangeUnconditional

namespace StrongExchangeUnconditional

/--
[not_descent_length_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/StrongExchangeUnconditional.lean)
-/
@[path]
lemma not_descent_length_eq
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v : W}
  {i : B}
-- given
  (h : ¬cs.IsRightDescent v i) :
-- imply
  cs.length (v * cs.simple i) = cs.length v + 1 := by
-- proof
  unfold CoxeterSystem.IsRightDescent at h
  push Not at h
  obtain h1 | h1 <;> omega := cs.length_mul_simple v i

end StrongExchangeUnconditional

namespace StrongExchangeUnconditional

/--
[descent_length_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/StrongExchangeUnconditional.lean)
-/
@[path]
lemma descent_length_eq
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {w : W}
  {i : B}
-- given
  (h : cs.IsRightDescent w i) :
-- imply
  cs.length (w * cs.simple i) + 1 = cs.length w := by
-- proof
  unfold CoxeterSystem.IsRightDescent at h
  obtain h1 | h1 <;> omega := cs.length_mul_simple w i

end StrongExchangeUnconditional

namespace StrongExchangeUnconditional

/--
[reflection_identification_core](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/StrongExchangeUnconditional.lean)
-/
@[path]
lemma reflection_identification_core
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {v w t : M.Group}
  {i : B}
-- given
  (ht : t ∈ CoxeterBruhat.reflections M M.toCoxeterSystem)
  (hvt : v * t = w)
  (hlen : M.toCoxeterSystem.length v + 1 = M.toCoxeterSystem.length w)
  (hv_asc : ¬M.toCoxeterSystem.IsRightDescent v i)
  (hw_desc : M.toCoxeterSystem.IsRightDescent w i) :
-- imply
  t = M.toCoxeterSystem.simple i := by
-- proof
  set cs := M.toCoxeterSystem
  have ht_inv : t * t = 1 := CoxeterBruhat.reflection_sq cs ht
  have hwt_eq_v : w * t = v := by
    have : w * t = (v * t) * t := by rw [hvt]
    rw [this, mul_assoc, ht_inv, mul_one]
  obtain ⟨u, j, htdef⟩ := ht
  obtain ⟨word_u, hred_u, hprod_u⟩ := cs.exists_isReduced u
  have key : ∃ word_u₀ : List B,
    CoxeterGroup.IsPositive (CoxeterGroup.wordSigma M word_u₀ (CoxeterGroup.e j)) ∧
    t = cs.wordProd word_u₀ * cs.simple j * (cs.wordProd word_u₀)⁻¹ := by
    by_cases hu_desc : cs.IsRightDescent u j
    ·
      refine ⟨word_u ++ [j], ?_, ?_⟩
      ·
        rw [CoxeterGroup.wordSigma_append, CoxeterGroup.wordSigma_singleton]
        have hsig : CoxeterGroup.sigma M j (CoxeterGroup.e j) = fun t => -(CoxeterGroup.e j t) :=
          CoxeterGroup.sigma_e_self M j
        rw [hsig]
        have : (fun t => -(CoxeterGroup.e j t)) = -(CoxeterGroup.e j) := by ext t; simp
        rw [this]
        have := CoxeterGroup.wordSigma_smul M word_u (-1 : ℝ) (CoxeterGroup.e j)
        simp at this
        rw [this]
        rw [CoxeterGroup.neg_isPositive_iff]
        exact DescentInversionBridge.descent_implies_isNegative M cs word_u j hred_u
          (by rw [← hprod_u]; exact hu_desc)
      ·
        rw [cs.wordProd_append, cs.wordProd_singleton, ← hprod_u, htdef]
        group
    ·
      refine ⟨word_u, ?_, ?_⟩
      · exact DescentInversionBridge.ascent_implies_isPositive M cs word_u j hred_u
        (by rw [← hprod_u]; exact hu_desc)
      · rw [htdef, ← hprod_u]
  obtain ⟨word_u₀, hα_pos, htdef₀⟩ := key
  set α := CoxeterGroup.wordSigma M word_u₀ (CoxeterGroup.e j) with hα_def
  have hform_α : CoxeterGroup.bilinForm M α α = 1 := by
    rw [hα_def, CoxeterGroup.wordSigma_preserves_form,
      CoxeterGroup.bilinForm_e_e, CoxeterGroup.formVal_diag]
  obtain ⟨prefix_, hred_pi, hprod_pi⟩ :=
    StrongExchangeBridge.exists_reduced_word_ending_in_descent (cs := cs) w i hw_desc
  have hlen_wt : cs.length (w * t) < cs.length w := by
    rw [hwt_eq_v]; omega
  have hlen_desc : cs.length (cs.wordProd (prefix_ ++ [i]) *
    (cs.wordProd word_u₀ * cs.simple j * (cs.wordProd word_u₀)⁻¹)) <
    cs.length (cs.wordProd (prefix_ ++ [i])) := by
    rw [hprod_pi, ← htdef₀]; exact hlen_wt
  have hneg_w : CoxeterGroup.IsNegative (CoxeterGroup.wordSigma M (prefix_ ++ [i]) α) :=
    CoxeterGroup.neg_of_descent_reflection M cs (prefix_ ++ [i]) word_u₀ j hred_pi hα_pos hlen_desc
  have hdecomp : CoxeterGroup.wordSigma M (prefix_ ++ [i]) α =
    CoxeterGroup.wordSigma M prefix_ (CoxeterGroup.sigma M i α) := by
    rw [CoxeterGroup.wordSigma_append, CoxeterGroup.wordSigma_singleton]
  rw [hdecomp] at hneg_w
  have hσiα_neg : CoxeterGroup.IsNegative (CoxeterGroup.sigma M i α) := by
    by_contra hσiα_not_neg
    have hσiα_eq : CoxeterGroup.sigma M i α =
      CoxeterGroup.wordSigma M ([i] ++ word_u₀) (CoxeterGroup.e j) := by
      rw [CoxeterGroup.wordSigma_append, CoxeterGroup.wordSigma_singleton, hα_def]
    have hlen_sigu : cs.length (cs.wordProd ([i] ++ word_u₀) * cs.simple j) <
      cs.length (cs.wordProd ([i] ++ word_u₀)) ∨
      cs.length (cs.wordProd ([i] ++ word_u₀) * cs.simple j) >
      cs.length (cs.wordProd ([i] ++ word_u₀)) := by
      have := cs.length_mul_simple (cs.wordProd ([i] ++ word_u₀)) j
      omega
    obtain ⟨word_iu, hred_iu, hprod_iu⟩ := cs.exists_isReduced (cs.wordProd ([i] ++ word_u₀))
    obtain hdesc_iu | hasc_iu := hlen_sigu
    ·
      exfalso; apply hσiα_not_neg
      have hneg_iu : CoxeterGroup.IsNegative (CoxeterGroup.wordSigma M word_iu (CoxeterGroup.e j)) :=
        DescentInversionBridge.descent_implies_isNegative M cs word_iu j hred_iu
          (by rw [← hprod_iu]; exact hdesc_iu)
      rw [hσiα_eq]
      rwa [DescentInversionBridge.wordSigma_eq_of_wordProd_eq M cs ([i] ++ word_u₀) word_iu
        (by rw [← hprod_iu]) (CoxeterGroup.e j)]
    ·
      exfalso
      have hσiα_pos : CoxeterGroup.IsPositive (CoxeterGroup.sigma M i α) := by
        rw [hσiα_eq]
        have hpos_iu : CoxeterGroup.IsPositive (CoxeterGroup.wordSigma M word_iu (CoxeterGroup.e j)) :=
          DescentInversionBridge.ascent_implies_isPositive M cs word_iu j hred_iu
            (by rw [← hprod_iu]; intro h; exact Nat.lt_irrefl _ (lt_trans h hasc_iu))
        rwa [DescentInversionBridge.wordSigma_eq_of_wordProd_eq M cs ([i] ++ word_u₀) word_iu
          (by rw [← hprod_iu]) (CoxeterGroup.e j)]
      have hred_prefix : cs.IsReduced prefix_ :=
        isReduced_of_append_isReduced cs prefix_ i hred_pi
      have hprod_prefix : cs.wordProd prefix_ = w * cs.simple i := by
        have h1 : cs.wordProd (prefix_ ++ [i]) = cs.wordProd prefix_ * cs.simple i := by
          rw [cs.wordProd_append, cs.wordProd_singleton]
        rw [hprod_pi] at h1
        have : cs.wordProd prefix_ = w * (cs.simple i)⁻¹ := by
          rw [h1]; group
        rw [this, show (cs.simple i)⁻¹ = cs.simple i from by
          have : cs.simple i * cs.simple i = 1 := cs.simple_mul_simple_self i
          exact inv_eq_of_mul_eq_one_right this]
      have hascent_len : cs.length (cs.wordProd prefix_ *
        (cs.wordProd ([i] ++ word_u₀) * cs.simple j * (cs.wordProd ([i] ++ word_u₀))⁻¹)) >
        cs.length (cs.wordProd prefix_) := by
        have hprod_iu : cs.wordProd ([i] ++ word_u₀) = cs.simple i * cs.wordProd word_u₀ := by
          rw [cs.wordProd_append, cs.wordProd_singleton]
        have hconj : cs.wordProd ([i] ++ word_u₀) * cs.simple j * (cs.wordProd ([i] ++ word_u₀))⁻¹ =
          cs.simple i * (cs.wordProd word_u₀ * cs.simple j * (cs.wordProd word_u₀)⁻¹) * cs.simple i := by
          rw [hprod_iu]; group
          have hsi_inv : cs.simple i ^ (-1 : ℤ) = cs.simple i := by
            rw [zpow_neg_one]
            exact inv_eq_of_mul_eq_one_right (cs.simple_mul_simple_self i)
          rw [hsi_inv]
        rw [hprod_prefix, hconj]
        have : w * cs.simple i * (cs.simple i * (cs.wordProd word_u₀ * cs.simple j *
          (cs.wordProd word_u₀)⁻¹) * cs.simple i) = v * cs.simple i := by
          have hsi_sq : cs.simple i * cs.simple i = 1 := cs.simple_mul_simple_self i
          rw [← htdef₀]
          calc w * cs.simple i * (cs.simple i * t * cs.simple i)
            = w * (cs.simple i * cs.simple i) * t * cs.simple i := by group
            _ = w * 1 * t * cs.simple i := by rw [hsi_sq]
            _ = (w * t) * cs.simple i := by group
            _ = v * cs.simple i := by rw [hwt_eq_v]
        rw [this]
        have hlen_vsi := not_descent_length_eq cs v i hv_asc
        have hlen_wsi := descent_length_eq cs w i hw_desc
        omega
      have hpos_prefix : CoxeterGroup.IsPositive
        (CoxeterGroup.wordSigma M prefix_ (CoxeterGroup.wordSigma M ([i] ++ word_u₀) (CoxeterGroup.e j))) :=
        CoxeterGroup.pos_of_ascent_reflection M cs prefix_ ([i] ++ word_u₀) j hred_prefix hσiα_pos hascent_len
      rw [hσiα_eq] at hneg_w
      have hzero := CoxeterSignChangeExchangeFinal.isPositive_isNegative_eq_zero hpos_prefix hneg_w
      have hform_prefix : CoxeterGroup.bilinForm M
        (CoxeterGroup.wordSigma M prefix_ (CoxeterGroup.wordSigma M ([i] ++ word_u₀) (CoxeterGroup.e j)))
        (CoxeterGroup.wordSigma M prefix_ (CoxeterGroup.wordSigma M ([i] ++ word_u₀) (CoxeterGroup.e j))) = 1 := by
        rw [CoxeterGroup.wordSigma_preserves_form, CoxeterGroup.wordSigma_preserves_form,
          CoxeterGroup.bilinForm_e_e, CoxeterGroup.formVal_diag]
      rw [hzero] at hform_prefix
      simp [CoxeterGroup.bilinForm] at hform_prefix
  have hα_eq_ei : α = CoxeterGroup.e i :=
    CoxeterSignChangeExchangeFinal.isPositive_sigma_isNegative_eq_e M i α hα_pos hσiα_neg hform_α
  have hcommute : cs.simple i * cs.wordProd word_u₀ = cs.wordProd word_u₀ * cs.simple j :=
    CoxeterSignChangeExchangeFinal.wordProd_cons_eq_append_of_wordSigma_eq_e cs word_u₀ j i
      (by rw [← hα_def]; exact hα_eq_ei)
  rw [htdef₀]
  symm
  calc cs.simple i = (cs.simple i * cs.wordProd word_u₀) * (cs.wordProd word_u₀)⁻¹ := by group
    _ = (cs.wordProd word_u₀ * cs.simple j) * (cs.wordProd word_u₀)⁻¹ := by rw [hcommute]
    _ = cs.wordProd word_u₀ * cs.simple j * (cs.wordProd word_u₀)⁻¹ := by group

end StrongExchangeUnconditional

namespace StrongExchangeUnconditional

/--
[inversionDifferenceBridge_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/StrongExchangeUnconditional.lean)
-/
@[path]
lemma inversionDifferenceBridge_unconditional
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  InversionDifferenceBridgeHyp (M.toCoxeterSystem) :=
-- proof
  ⟨fun v w t ht hvt hlen i hv hw =>
    reflection_identification_core M v w t ht hvt hlen i hv hw⟩

end StrongExchangeUnconditional

namespace StrongExchangeUnconditional

/--
[reflectionIdentificationHyp_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/StrongExchangeUnconditional.lean)
-/
@[path]
lemma reflectionIdentificationHyp_unconditional
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  CoxeterBruhat.ReflectionIdentificationHyp (M.toCoxeterSystem) :=
-- proof
  reflection_identification_genuine
    (inversionDifferenceBridge_unconditional M)

end StrongExchangeUnconditional

namespace StrongExchangeUnconditional

/--
[strongExchangeForBruhat_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/StrongExchangeUnconditional.lean)
-/
@[path]
lemma strongExchangeForBruhat_unconditional
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  CoxeterBruhat.StrongExchangeForBruhat (M.toCoxeterSystem) :=
-- proof
  CoxeterBruhat.strong_exchange_of_reflection_id M.toCoxeterSystem
    (reflectionIdentificationHyp_unconditional M)

end StrongExchangeUnconditional


-- created on 2026-10-23
