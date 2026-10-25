import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.HasseWalks
open HasseWalks


namespace HasseWalks

/--
[expandBlock_toInt_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma expandBlock_toInt_sum
  {p : ℕ × ℕ} :
-- imply
  ((expandBlock p).map HStep.toInt).sum = (p.1 : ℤ) - (p.2 : ℤ) := by
-- proof
  simp only [expandBlock, HStep.toInt, List.map_append, List.sum_append,
    List.map_replicate, List.sum_replicate, nsmul_eq_mul, mul_one]
  omega

end HasseWalks

namespace HasseWalks

/--
[expandBlocks_toInt_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma expandBlocks_toInt_sum
  {w : List (ℕ × ℕ)} :
-- imply
  ((expandBlocks w).map HStep.toInt).sum = displacement w := by
-- proof
  induction w with
  | nil => simp [expandBlocks, displacement]
  | cons p w ih =>
    simp only [expandBlocks, displacement]
    simp only [List.flatMap_cons, List.map_append, List.sum_append, expandBlock_toInt_sum,
      List.map_cons, List.sum_cons]
    have : (List.flatMap expandBlock w).map HStep.toInt = (expandBlocks w).map HStep.toInt := rfl
    rw [this, ih, displacement]

end HasseWalks

namespace HasseWalks

/--
[expandBlocks_append](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma expandBlocks_append
  {w₁ w₂ : List (ℕ × ℕ)} :
-- imply
  expandBlocks (w₁ ++ w₂) = expandBlocks w₁ ++ expandBlocks w₂ := by
-- proof
  simp only [expandBlocks, List.flatMap_append]

end HasseWalks

namespace HasseWalks

/--
[walk_card_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma walk_card_step
  {steps : List HStep}
  {start target : YoungDiagram}
  {walk : HasseWalk steps start target}
  {i : Fin steps.length} :
-- imply
  ((walk.diagram ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩).card : ℤ) = ((walk.diagram ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).card : ℤ) + (steps[i]).toInt := by
-- proof
  cases h_step : steps[i] with
  | U =>
    have := card_covBy_succ (walk.step_up i h_step)
    simp only [HStep.toInt]; omega
  | D =>
    have := card_covBy_succ (walk.step_down i h_step)
    simp only [HStep.toInt]; omega

end HasseWalks

namespace HasseWalks

/--
[walk_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma walk_card_eq
  {steps : List HStep}
  {start target : YoungDiagram}
  {walk : HasseWalk steps start target}
  {k : ℕ}
-- given
  (hk : k ≤ steps.length) :
-- imply
  ((walk.diagram ⟨k, Nat.lt_succ_of_le hk⟩).card : ℤ) = (start.card : ℤ) + ((steps.take k).map HStep.toInt).sum := by
-- proof
  induction k with
  | zero =>
    simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero]
    exact congrArg (fun d => (d.card : ℤ)) walk.start_eq
  | succ n ih =>
    have hn_lt : n < steps.length := Nat.lt_of_succ_le hk
    have h_step := walk_card_step walk ⟨n, hn_lt⟩
    rw [h_step, ih (Nat.le_of_lt hn_lt)]
    rw [← List.take_concat_get' steps n hn_lt]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, add_assoc, Fin.getElem_fin]

end HasseWalks

namespace HasseWalks

/--
[walk_exists_necessity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma walk_exists_necessity
  {w : List (ℕ × ℕ)}
  {lam : YoungDiagram}
  {n : ℕ}
  {walk : HasseWalk (expandBlocks w) ⊥ lam}
-- given
  (hn : lam.card = n) :
-- imply
  IsValidWord w n := by
-- proof
  have h_bot_card : (⊥ : YoungDiagram).card = 0 := by simp [YoungDiagram.card]
  constructor
  · have h_end := walk_card_eq walk (expandBlocks w).length le_rfl
    simp only [walk.target_eq, List.take_length] at h_end
    rwa [hn, h_bot_card, Nat.cast_zero, zero_add, expandBlocks_toInt_sum] at h_end
  · intro j _ hj_le
    set pos := (expandBlocks (w.take j)).length
    have hpos_le : pos ≤ (expandBlocks w).length := by
      have : expandBlocks w = expandBlocks (w.take j) ++ expandBlocks (w.drop j) := by
        rw [← expandBlocks_append, List.take_append_drop]
      rw [this]; simp only [List.length_append, pos]; omega
    have h_pos := walk_card_eq walk pos hpos_le
    rw [h_bot_card, Nat.cast_zero, zero_add] at h_pos
    have h_take : (expandBlocks w).take pos = expandBlocks (w.take j) := by
      conv_lhs => rw [← List.take_append_drop j w, expandBlocks_append]
      exact List.take_left
    rw [h_take, expandBlocks_toInt_sum] at h_pos
    show 0 ≤ partialDisplacement w j
    rw [show partialDisplacement w j = displacement (w.take j) from rfl, ← h_pos]
    exact Int.natCast_nonneg _

end HasseWalks

namespace HasseWalks

/--
[card_zero_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma card_zero_eq_bot
  {μ : YoungDiagram}
-- given
  (h : μ.card = 0) :
-- imply
  μ = ⊥ := by
-- proof
  ext ⟨i, j⟩; constructor
  · intro hmem; exact absurd h (Finset.card_ne_zero_of_mem hmem)
  · intro hmem; exact absurd hmem (YoungDiagram.notMem_bot _)

end HasseWalks

namespace HasseWalks

/--
[exists_removable_cell](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma exists_removable_cell
  {ν : YoungDiagram}
-- given
  (hne : ν.cells.Nonempty) :
-- imply
  ∃ c ∈ ν.cells, (c.1 + 1, c.2) ∉ ν.cells ∧ (c.1, c.2 + 1) ∉ ν.cells := by
-- proof
  set f : ℕ × ℕ → ℕ := fun p => p.1 + p.2
  have img_ne := hne.image f
  obtain ⟨c, hc, hc_max⟩ : ∃ c ∈ ν.cells, f c =
    (ν.cells.image f).max' img_ne := by
    have := Finset.max'_mem _ img_ne
    rw [Finset.mem_image] at this
    obtain ⟨c, hc, hceq⟩ := this
    exact ⟨c, hc, hceq⟩
  refine ⟨c, hc, ?_, ?_⟩
  · intro h
    have hle := Finset.le_max' (ν.cells.image f) (f (c.1 + 1, c.2))
      (Finset.mem_image.mpr ⟨(c.1 + 1, c.2), h, rfl⟩)
    simp only [f] at hle hc_max; omega
  · intro h
    have hle := Finset.le_max' (ν.cells.image f) (f (c.1, c.2 + 1))
      (Finset.mem_image.mpr ⟨(c.1, c.2 + 1), h, rfl⟩)
    simp only [f] at hle hc_max; omega

end HasseWalks

namespace HasseWalks

/--
[isLowerSet_erase_corner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma isLowerSet_erase_corner
  {ν : YoungDiagram}
  {c : ℕ × ℕ}
-- given
  (hc : c ∈ ν.cells)
  (h0 : (c.1 + 1, c.2) ∉ ν.cells)
  (h1 : (c.1, c.2 + 1) ∉ ν.cells) :
-- imply
  IsLowerSet ((ν.cells.erase c : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
-- proof
  intro a b hab ha_mem
  rw [Finset.mem_coe, Finset.mem_erase] at ha_mem ⊢
  obtain ⟨ha_ne, ha_ν⟩ := ha_mem
  refine ⟨?_, ν.isLowerSet hab ha_ν⟩
  intro hb_eq; rw [hb_eq] at hab
  have ha1 : c.1 ≤ a.1 := hab.1
  have ha2 : c.2 ≤ a.2 := hab.2
  obtain ha1_lt | ha1_eq := Nat.lt_or_eq_of_le ha1
  · exact h1 (ν.isLowerSet (show (c.1 + 1, c.2) ≤ a from ⟨ha1_lt, ha2⟩) ha_ν)
  · rcases Nat.lt_or_eq_of_le ha2 with ha2_lt | ha2_eq
    · exact h2 (ν.isLowerSet (show (c.1, c.2 + 1) ≤ a from ⟨ha1, ha2_lt⟩) ha_ν)
    · exact ha_ne (Prod.ext ha1_eq.symm ha2_eq.symm)

end HasseWalks

namespace HasseWalks

/--
[covBy_erase_corner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma covBy_erase_corner
  {ν : YoungDiagram}
  {c : ℕ × ℕ}
-- given
  (hc : c ∈ ν.cells)
  (h0 : (c.1 + 1, c.2) ∉ ν.cells)
  (h1 : (c.1, c.2 + 1) ∉ ν.cells) :
-- imply
  (⟨ν.cells.erase c, isLowerSet_erase_corner ν c hc h0 h1⟩ : YoungDiagram) ⋖ ν := by
-- proof
  constructor
  · show (⟨ν.cells.erase c, _⟩ : YoungDiagram) < ν
    exact Finset.erase_ssubset hc
  · intro ξ hlt hξν
    have h_sub_ν : ξ.cells ⊆ ν.cells := hξν.le
    have : (ν.cells.erase c).card + 1 ≤ ξ.cells.card := Finset.card_lt_card hlt
    have : ξ.cells = ν.cells :=
      Finset.eq_of_subset_of_card_le h_sub_ν (by
        rw [Finset.card_erase_of_mem hc] at *; omega)
    exact absurd (YoungDiagram.ext_iff.mpr this) (ne_of_lt hξν)

end HasseWalks

namespace HasseWalks

/--
[exists_covBy_below](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma exists_covBy_below
  {ν : YoungDiagram}
-- given
  (hν : 0 < ν.card) :
-- imply
  ∃ μ : YoungDiagram, μ ⋖ ν := by
-- proof
  have hne : ν.cells.Nonempty := Finset.card_pos.mp hν
  obtain ⟨c, hc, h1, h2⟩ := exists_removable_cell ν hne
  exact ⟨⟨ν.cells.erase c, isLowerSet_erase_corner ν c hc h1 h2⟩,
    covBy_erase_corner ν c hc h1 h2⟩

end HasseWalks

namespace HasseWalks

/--
[exists_covBy_above](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma exists_covBy_above
  {μ : YoungDiagram} :
-- imply
  ∃ ν : YoungDiagram, μ ⋖ ν := by
-- proof
  set c := (0, μ.rowLen 0) with hc_def
  have hc_not_mem : c ∉ μ.cells := by
    simp only [YoungDiagram.mem_cells, hc_def]
    rw [YoungDiagram.mem_iff_lt_rowLen]; omega
  set ν : YoungDiagram := ⟨Finset.cons c μ.cells hc_not_mem,
    by
      intro a b hab hb_mem
      rw [Finset.mem_coe, Finset.mem_cons] at hb_mem ⊢
      obtain hb_eq | hb_μ := hb_mem
      · subst hb_eq
        have ha1_eq : b.1 = 0 := Nat.le_zero.mp hab.1
        obtain ha2_lt | ha2_eq := Nat.lt_or_eq_of_le hab.2
        · right; rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, ha1_eq]
          exact ha2_lt
        · left; exact Prod.ext ha1_eq ha2_eq
      · right; exact μ.isLowerSet hab hb_μ⟩ with hν_def
  refine ⟨ν, ?_⟩
  constructor
  · show μ < ν
    exact Finset.ssubset_cons hc_not_mem
  · intro ξ hμ_lt_ξ hξ_lt_ν
    have hξ_le_ν : ξ.cells ⊆ ν.cells := hξ_lt_ν.le
    have : μ.cells.card + 1 ≤ ξ.cells.card := Finset.card_lt_card hμ_lt_ξ
    have hν_card : ν.cells.card = μ.cells.card + 1 := by
      show (Finset.cons c μ.cells hc_not_mem).card = μ.cells.card + 1
      exact Finset.card_cons hc_not_mem
    have : ξ.cells = ν.cells := by
      apply Finset.eq_of_subset_of_card_le hξ_le_ν; omega
    exact absurd (YoungDiagram.ext_iff.mpr this) (ne_of_lt hξ_lt_ν)

end HasseWalks

namespace HasseWalks

/--
[nonempty_walk_extend](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma nonempty_walk_extend
  {s : List HStep}
  {a : HStep}
  {mid target : YoungDiagram}
-- given
  (hw : Nonempty (HasseWalk s ⊥ mid))
  (hU : a = HStep.U → mid ⋖ target)
  (hD : a = HStep.D → target ⋖ mid) :
-- imply
  Nonempty (HasseWalk (s ++ [a]) ⊥ target) := by
-- proof
  obtain ⟨w⟩ := hw
  refine ⟨⟨fun ⟨i, hi⟩ => if h : i < s.length + 1 then w.diagram ⟨i, h⟩ else target,
    ?_, ?_, ?_, ?_⟩⟩
  · dsimp only; rw [dif_pos (by omega : 0 < s.length + 1)]; exact w.start_eq
  · dsimp only; exact dif_neg (by simp)
  · intro ⟨i, hi_orig⟩ hstep
    dsimp only
    have hlen_eq : (s ++ [a]).length = s.length + 1 := by simp
    have hi : i < s.length + 1 := by omega
    by_cases hi' : i + 1 < s.length + 1
    · rw [dif_pos (show i < s.length + 1 from hi), dif_pos hi']
      have hi_s : i < s.length := by omega
      have hstep' : s[i]'hi_s = HStep.U := by
        have h := @List.getElem_append _ s [a] i hi_orig
        rw [dif_pos hi_s] at h; rw [← h]; exact hstep
      exact w.step_up ⟨i, hi_s⟩ hstep'
    · rw [dif_pos (show i < s.length + 1 from hi), dif_neg hi']
      have hi_eq : i = s.length := by omega
      subst hi_eq; rw [w.target_eq]; apply hU
      have h := @List.getElem_append _ s [a] s.length hi_orig
      rw [dif_neg (by omega : ¬ s.length < s.length)] at h
      simp only [Nat.sub_self, List.getElem_cons_zero] at h
      rw [← h]; exact hstep
  · intro ⟨i, hi_orig⟩ hstep
    dsimp only
    have hlen_eq : (s ++ [a]).length = s.length + 1 := by simp
    have hi : i < s.length + 1 := by omega
    by_cases hi' : i + 1 < s.length + 1
    · rw [dif_pos (show i < s.length + 1 from hi), dif_pos hi']
      have hi_s : i < s.length := by omega
      have hstep' : s[i]'hi_s = HStep.D := by
        have h := @List.getElem_append _ s [a] i hi_orig
        rw [dif_pos hi_s] at h; rw [← h]; exact hstep
      exact w.step_down ⟨i, hi_s⟩ hstep'
    · rw [dif_pos (show i < s.length + 1 from hi), dif_neg hi']
      have hi_eq : i = s.length := by omega
      subst hi_eq; rw [w.target_eq]; apply hD
      have h := @List.getElem_append _ s [a] s.length hi_orig
      rw [dif_neg (by omega : ¬ s.length < s.length)] at h
      simp only [Nat.sub_self, List.getElem_cons_zero] at h
      rw [← h]; exact hstep

end HasseWalks

namespace HasseWalks

/--
[walk_from_bot_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma walk_from_bot_exists
  {s : List HStep}
  {target : YoungDiagram}
-- given
  (hcard : (target.card : ℤ) = ((s.map HStep.toInt).sum))
  (hpartial : ∀ k, k ≤ s.length → 0 ≤ ((s.take k).map HStep.toInt).sum) :
-- imply
  Nonempty (HasseWalk s ⊥ target) := by
-- proof
  induction s using List.reverseRecOn generalizing target with
  | nil =>
    have hcard0 : target.card = 0 := by
      have : (target.card : ℤ) = 0 := by convert hcard using 1
      exact_mod_cast this
    have := card_zero_eq_bot hcard0; subst this
    exact ⟨⟨fun _ => ⊥, rfl, rfl, fun i => i.elim0, fun i => i.elim0⟩⟩
  | append_singleton s a ih =>
    cases a with
    | U =>
      have hsum_s : ((s.map HStep.toInt).sum) = (target.card : ℤ) - 1 := by
        simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_cons,
          List.sum_nil, add_zero, HStep.toInt] at hcard; linarith
      have htgt_pos : 0 < target.card := by
        have h := hpartial s.length (by simp)
        rw [List.take_append_of_le_length (by omega), List.take_length] at h; linarith
      obtain ⟨mid, hmid⟩ := exists_covBy_below htgt_pos
      have hccs := card_covBy_succ hmid
      have hcard_mid : (mid.card : ℤ) = (s.map HStep.toInt).sum := by omega
      have hpartial_s : ∀ k, k ≤ s.length → 0 ≤ ((s.take k).map HStep.toInt).sum := by
        intro k hk
        have h := hpartial k (by simp; omega)
        rwa [List.take_append_of_le_length (by omega)] at h
      exact nonempty_walk_extend (ih mid hcard_mid hpartial_s)
        (fun _ => hmid) (fun h => absurd h (by decide))
    | D =>
      have hsum_s : ((s.map HStep.toInt).sum) = (target.card : ℤ) + 1 := by
        simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_cons,
          List.sum_nil, add_zero, HStep.toInt] at hcard; linarith
      obtain ⟨mid, hmid⟩ := exists_covBy_above target
      have hccs := card_covBy_succ hmid
      have hcard_mid : (mid.card : ℤ) = (s.map HStep.toInt).sum := by omega
      have hpartial_s : ∀ k, k ≤ s.length → 0 ≤ ((s.take k).map HStep.toInt).sum := by
        intro k hk
        have h := hpartial k (by simp; omega)
        rwa [List.take_append_of_le_length (by omega)] at h
      exact nonempty_walk_extend (ih mid hcard_mid hpartial_s)
        (fun h => absurd h (by decide)) (fun _ => hmid)

end HasseWalks

namespace HasseWalks

/--
[expandBlocks_partial_nonneg_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma expandBlocks_partial_nonneg_aux
  {w : List (ℕ × ℕ)}
  {base : ℤ}
  {k : ℕ}
-- given
  (hbase : 0 ≤ base)
  (hpartial : ∀ j, 1 ≤ j → j ≤ w.length → 0 ≤ base + partialDisplacement w j)
  (hk : k ≤ (expandBlocks w).length) :
-- imply
  0 ≤ base + (((expandBlocks w).take k).map HStep.toInt).sum := by
-- proof
  induction w generalizing k base with
  | nil =>
    simp only [expandBlocks, List.flatMap_nil, List.length_nil] at hk
    have : k = 0 := Nat.le_zero.mp hk
    subst this; simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero]; exact hbase
  | cons p w' ih =>
    simp only [expandBlocks, List.flatMap_cons] at hk ⊢
    by_cases hk' : k ≤ (expandBlock p).length
    · rw [List.take_append_of_le_length hk']
      simp only [expandBlock, List.length_append, List.length_replicate] at hk'
      by_cases hk_u : k ≤ p.1
      · have htake : (List.replicate p.1 HStep.U ++ List.replicate p.2 HStep.D).take k =
        (List.replicate p.1 HStep.U).take k :=
        List.take_append_of_le_length (by simp; omega)
        simp only [expandBlock, htake, List.take_replicate, List.map_replicate,
          HStep.toInt, List.sum_replicate, nsmul_eq_mul, mul_one, Nat.min_eq_left hk_u]
        linarith [Int.natCast_nonneg k]
      · push Not at hk_u
        have htake : (List.replicate p.1 HStep.U ++ List.replicate p.2 HStep.D).take k =
          List.replicate p.1 HStep.U ++
          (List.replicate p.2 HStep.D).take (k - p.1) := by
          rw [List.take_append, List.take_replicate]
          simp only [List.length_replicate, Nat.min_eq_right (by omega : p.1 ≤ k)]
        simp only [expandBlock, htake, List.map_append, List.sum_append,
          List.map_replicate, HStep.toInt, List.sum_replicate, nsmul_eq_mul, mul_one,
          List.take_replicate]
        have hdisp := hpartial 1 (by omega) (by simp)
        simp only [partialDisplacement, displacement, List.take_succ_cons,
          List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero] at hdisp
        have hmin : (↑(min (k - p.1) p.2) : ℤ) ≤ (p.2 : ℤ) := by
          exact_mod_cast Nat.min_le_right _ _
        linarith
    · push Not at hk'
      rw [List.take_append, List.map_append, List.sum_append,
        List.take_of_length_le (by omega)]
      rw [expandBlock_toInt_sum]
      have hbase' : 0 ≤ base + ((p.1 : ℤ) - (p.2 : ℤ)) := by
        have hdisp := hpartial 1 (by omega) (by simp)
        simp only [partialDisplacement, displacement, List.take_succ_cons,
          List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero] at hdisp
        linarith
      have hpartial' : ∀ j, 1 ≤ j → j ≤ w'.length →
        0 ≤ (base + ((p.1 : ℤ) - (p.2 : ℤ))) + partialDisplacement w' j := by
        intro j hj1 hj2
        have := hpartial (j + 1) (by omega) (by simp; omega)
        simp only [partialDisplacement, List.take_succ_cons] at this ⊢
        simp only [displacement, List.map_cons, List.sum_cons] at this
        rw [displacement]; linarith
      have hk_tail : k - (expandBlock p).length ≤ (expandBlocks w').length := by
        change k - _ ≤ (List.flatMap expandBlock w').length
        have : (expandBlock p ++ List.flatMap expandBlock w').length =
          (expandBlock p).length + (List.flatMap expandBlock w').length :=
          List.length_append
        omega
      have ih_applied := ih (base + ((p.1 : ℤ) - (p.2 : ℤ))) hbase' hpartial'
        (k - (expandBlock p).length) hk_tail
      have : expandBlocks w' = List.flatMap expandBlock w' := rfl
      rw [this] at ih_applied
      linarith

end HasseWalks

namespace HasseWalks

/--
[walk_exists_sufficiency](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma walk_exists_sufficiency
  {w : List (ℕ × ℕ)}
  {lam : YoungDiagram}
  {n : ℕ}
-- given
  (hn : lam.card = n)
  (hvalid : IsValidWord w n) :
-- imply
  Nonempty (HasseWalk (expandBlocks w) ⊥ lam) := by
-- proof
  apply walk_from_bot_exists
  · rw [expandBlocks_toInt_sum, hn]; exact hvalid.1.symm
  · intro k hk
    have := expandBlocks_partial_nonneg_aux w 0 (le_refl _)
      (fun j hj1 hj2 => by simp only [zero_add]; exact hvalid.2 j hj1 hj2) k hk
    simp only [zero_add] at this; exact this

end HasseWalks

namespace HasseWalks

/--
[valid_word_iff_walk_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
lemma valid_word_iff_walk_exists
  {w : List (ℕ × ℕ)}
  {lam : YoungDiagram}
  {n : ℕ}
-- given
  (hn : lam.card = n) :
-- imply
  Nonempty (HasseWalk (expandBlocks w) ⊥ lam) ↔ IsValidWord w n :=
-- proof
  ⟨fun ⟨walk⟩ => walk_exists_necessity w lam n hn walk,
    fun hvalid => walk_exists_sufficiency w lam n hn hvalid⟩

end HasseWalks

/--
[isLowerSet_insert_minimal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
private lemma isLowerSet_insert_minimal_eq
  {μ ν : YoungDiagram}
  {m : ℕ × ℕ}
-- given
  (hm_ν : m ∈ ν.cells)
  (hm_nμ : m ∉ μ.cells)
  (h_below : ∀ c : ℕ × ℕ, c ∈ ν.cells → c.1 ≤ m.1 → c.2 ≤ m.2 → c ≠ m → c ∈ μ.cells) :
-- imply
  IsLowerSet ((↑(Finset.cons m μ.cells hm_nμ)) : Set (ℕ × ℕ)) := by
-- proof
  apply HasseWalks.isLowerSet_insert_minimal m hm_ν hm_nμ h_below

/--
[card_covBy_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean)
-/
@[path]
private lemma card_covBy_succ_eq
  {μ ν : YoungDiagram}
-- given
  (h : μ ⋖ ν) :
-- imply
  ν.card = μ.card + 1 := by
-- proof
  apply HasseWalks.card_covBy_succ h


-- created on 2026-10-23
