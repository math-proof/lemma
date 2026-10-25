import Mathlib
import sympy.Basic
import Def.Topology.DescriptiveSetTheory.RationalsCharacterization
open Set Filter
open MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted


namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[dist_pos_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma dist_pos_of_ne {Z : Type*} [PseudoMetricSpace Z] [T2Space Z]
  {x y : Z} (h : x ≠ y) : 0 < dist x y := by
  by_contra hle
  rw [not_lt] at hle
  have h0 : dist x y = 0 := le_antisymm hle dist_nonneg
  obtain ⟨U, V, hUo, hVo, hxU, hyV, hUV⟩ := t2_separation h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hxU)
  have hyU : y ∈ U := hball (by rw [Metric.mem_ball, dist_comm, h0]; exact hε)
  have hmem : y ∈ U ∩ V := ⟨hyU, hyV⟩
  rw [disjoint_iff_inter_eq_empty.mp hUV] at hmem
  exact Set.notMem_empty y hmem

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[infinite_of_nonempty_open](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma infinite_of_nonempty_open {Z : Type*} [PseudoMetricSpace Z] [T1Space Z]
  [PerfectSpace Z] {U : Set Z} (hne : U.Nonempty) (hU : IsOpen U) : U.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨x, hxU⟩ := hne
  have hfin' : (U \ {x}).Finite := hfin.subset Set.sdiff_subset
  have hclosed : IsClosed (U \ {x}) := hfin'.isClosed
  have hsingle : ({x} : Set Z) = U ∩ (U \ {x})ᶜ := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_sdiff]
    constructor
    · intro h
      subst h
      exact ⟨hxU, fun h => h.2 rfl⟩
    · intro h
      by_contra hne'
      exact h.2 ⟨h.1, hne'⟩
  have hopen : IsOpen ({x} : Set Z) := by
    rw [hsingle]
    exact hU.inter (isOpen_compl_iff.mpr hclosed)
  have hbot : nhdsWithin x {x}ᶜ = ⊥ := by
    have hle : nhdsWithin x {x}ᶜ ≤ principal ({x} : Set Z) ⊓ principal ({x} : Set Z)ᶜ :=
      inf_le_inf (le_principal_iff.mpr (hopen.mem_nhds rfl)) le_rfl
    rw [inf_principal, Set.inter_compl_self, principal_empty] at hle
    exact le_bot_iff.mp hle
  exact Filter.not_neBot.mpr hbot (PerfectSpace.not_isolated x)

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[infinite_of_nonempty_clopen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma infinite_of_nonempty_clopen {Z : Type*} [PseudoMetricSpace Z] [T1Space Z]
  [PerfectSpace Z] {U : Set Z} (hne : U.Nonempty) (hU : IsClopen U) : U.Infinite :=
  infinite_of_nonempty_open hne hU.isOpen

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[nowhereDense_singleton_real](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma nowhereDense_singleton_real {d : ℝ} : IsNowhereDense ({d} : Set ℝ) := by
  have := PerfectSpace.not_isolated d
  change interior (closure {d}) = ∅
  rw [isClosed_singleton.closure_eq]
  exact interior_singleton d

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[exists_radius_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
in a countable pseudometric space. -/
private lemma exists_radius_avoid {Z : Type*} [PseudoMetricSpace Z] [Countable Z]
  (x : Z) {δ : ℝ} (hδ : 0 < δ) :
  ∃ r : ℝ, 0 < r ∧ r < δ ∧ ∀ y : Z, dist y x ≠ r := by
  by_contra hnone
  have hnone' : ∀ r : ℝ, 0 < r → r < δ → ∃ y : Z, dist y x = r := by
    intro r hr hrd
    by_contra hc
    rw [not_exists] at hc
    exact hnone ⟨r, hr, hrd, hc⟩
  have hsub : Set.Ioo (0 : ℝ) δ ⊆ Set.range (fun y : Z => dist y x) := by
    intro r hr
    rw [Set.mem_Ioo] at hr
    obtain ⟨y, hy⟩ := hnone' r hr.1 hr.2
    exact Set.mem_range.mpr ⟨y, hy⟩
  have hmeagre : IsMeagre (Set.range (fun y : Z => dist y x)) := by
    rw [← Set.iUnion_singleton_eq_range]
    apply isMeagre_iUnion
    intro y
    apply IsNowhereDense.isMeagre
    show IsNowhereDense ({dist y x} : Set ℝ)
    exact nowhereDense_singleton_real
  exact not_isMeagre_of_isOpen isOpen_Ioo (nonempty_Ioo.mpr hδ)
    (IsMeagre.mono hsub hmeagre)

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[exists_clopen_ball](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
arbitrarily small clopen ball around the point. -/
private lemma exists_clopen_ball {Z : Type*} [PseudoMetricSpace Z]
  [T2Space Z] [Countable Z] (x : Z) {U : Set Z} (hxU : x ∈ U) (hU : IsOpen U)
  {ε : ℝ} (hε : 0 < ε) :
  ∃ r : ℝ, 0 < r ∧ r < ε ∧ Metric.ball x r ⊆ U ∧ IsClopen (Metric.ball x r) := by
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  have hδ : (0 : ℝ) < min r₀ ε := lt_min hr₀ hε
  obtain ⟨r, hrpos, hrdelta, havoid⟩ := exists_radius_avoid (Z := Z) x hδ
  have hrε : r < ε := lt_of_lt_of_le hrdelta (min_le_right _ _)
  have hrr₀ : r ≤ r₀ := le_of_lt (lt_of_lt_of_le hrdelta (min_le_left _ _))
  refine ⟨r, hrpos, hrε, (Metric.ball_subset_ball hrr₀).trans hball₀, ?_⟩
  have hcb : Metric.closedBall x r = Metric.ball x r := by
    ext y
    rw [Metric.mem_closedBall, Metric.mem_ball]
    constructor
    · intro h
      obtain h' | h' := le_iff_lt_or_eq.mp h
      · exact h'
      · exact absurd h' (havoid y)
    · intro h
      exact le_of_lt h
  refine ⟨?_, Metric.isOpen_ball⟩
  rwa [← hcb]

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[exists_disjoint_clopen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma exists_disjoint_clopen {Z : Type*} [PseudoMetricSpace Z]
  [T2Space Z] [Countable Z] {W : Set Z} (hW : IsClopen W) {a b : Z}
  (ha : a ∈ W) (hb : b ∈ W) (hab : a ≠ b) {ε : ℝ} (hε : 0 < ε) :
  ∃ Ua Ub : Set Z, IsClopen Ua ∧ IsClopen Ub ∧ a ∈ Ua ∧ b ∈ Ub ∧ Ua ⊆ W ∧
    Ub ⊆ W ∧ Disjoint Ua Ub ∧ Ua ⊆ Metric.ball a ε ∧ Ub ⊆ Metric.ball b ε := by
  obtain ⟨Oa, Ob, hOao, hObo, haOa, hbOb, hdisj⟩ := t2_separation hab
  have hmem_a : a ∈ W ∩ Oa := ⟨ha, haOa⟩
  have hmem_b : b ∈ W ∩ Ob := ⟨hb, hbOb⟩
  obtain ⟨ra, hra0, hraε, hsuba, hcla⟩ :=
    exists_clopen_ball a hmem_a (hW.isOpen.inter hOao) hε
  obtain ⟨rb, hrb0, hrbε, hsubb, hclb⟩ :=
    exists_clopen_ball b hmem_b (hW.isOpen.inter hObo) hε
  refine ⟨Metric.ball a ra, Metric.ball b rb, hcla, hclb,
    Metric.mem_ball.mpr (by rw [dist_self]; exact hra0),
    Metric.mem_ball.mpr (by rw [dist_self]; exact hrb0),
    (subset_inter_iff.mp hsuba).1, (subset_inter_iff.mp hsubb).1, ?_, ?_, ?_⟩
  · apply hdisj.mono (subset_inter_iff.mp hsuba).2 (subset_inter_iff.mp hsubb).2
  · exact Metric.ball_subset_ball (le_of_lt hraε)
  · exact Metric.ball_subset_ball (le_of_lt hrbε)

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[exists_three_disjoint_clopen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
balls. -/
private lemma exists_three_disjoint_clopen {Z : Type*} [PseudoMetricSpace Z]
  [T2Space Z] [Countable Z] {W : Set Z} (hW : IsClopen W) {a b c : Z}
  (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W)
  (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {ε : ℝ} (hε : 0 < ε) :
  ∃ Ua Ub Uc : Set Z, IsClopen Ua ∧ IsClopen Ub ∧ IsClopen Uc ∧
    a ∈ Ua ∧ b ∈ Ub ∧ c ∈ Uc ∧ Ua ⊆ W ∧ Ub ⊆ W ∧ Uc ⊆ W ∧
    Disjoint Ua Ub ∧ Disjoint Ua Uc ∧ Disjoint Ub Uc ∧
    Ua ⊆ Metric.ball a ε ∧ Ub ⊆ Metric.ball b ε ∧ Uc ⊆ Metric.ball c ε := by
  obtain ⟨Oab1, Oab2, hOab1, hOab2, haOab1, hbOab2, hdisjAB⟩ := t2_separation hab
  obtain ⟨Oac1, Oac2, hOac1, hOac2, haOac1, hcOac2, hdisjAC⟩ := t2_separation hac
  obtain ⟨Obc1, Obc2, hObc1, hObc2, hbObc1, hcObc2, hdisjBC⟩ := t2_separation hbc
  have hOa : IsOpen (Oab1 ∩ Oac1) := hOab1.inter hOac1
  have hOb : IsOpen (Oab2 ∩ Obc1) := hOab2.inter hObc1
  have hOc : IsOpen (Oac2 ∩ Obc2) := hOac2.inter hObc2
  have haOa : a ∈ Oab1 ∩ Oac1 := ⟨haOab1, haOac1⟩
  have hbOb : b ∈ Oab2 ∩ Obc1 := ⟨hbOab2, hbObc1⟩
  have hcOc : c ∈ Oac2 ∩ Obc2 := ⟨hcOac2, hcObc2⟩
  have hdisjAB' : Disjoint (Oab1 ∩ Oac1) (Oab2 ∩ Obc1) :=
    hdisjAB.mono inter_subset_left inter_subset_left
  have hdisjAC' : Disjoint (Oab1 ∩ Oac1) (Oac2 ∩ Obc2) :=
    hdisjAC.mono inter_subset_right inter_subset_left
  have hdisjBC' : Disjoint (Oab2 ∩ Obc1) (Oac2 ∩ Obc2) :=
    hdisjBC.mono inter_subset_right inter_subset_right
  have hmem_a : a ∈ W ∩ (Oab1 ∩ Oac1) := ⟨ha, haOa⟩
  have hmem_b : b ∈ W ∩ (Oab2 ∩ Obc1) := ⟨hb, hbOb⟩
  have hmem_c : c ∈ W ∩ (Oac2 ∩ Obc2) := ⟨hc, hcOc⟩
  obtain ⟨ra, hra0, hraε, hsuba, hcla⟩ :=
    exists_clopen_ball a hmem_a (hW.isOpen.inter hOa) hε
  obtain ⟨rb, hrb0, hrbε, hsubb, hclb⟩ :=
    exists_clopen_ball b hmem_b (hW.isOpen.inter hOb) hε
  obtain ⟨rc, hrc0, hrcε, hsubc, hclc⟩ :=
    exists_clopen_ball c hmem_c (hW.isOpen.inter hOc) hε
  have haU : a ∈ Metric.ball a ra := Metric.mem_ball.mpr (by rw [dist_self]; exact hra0)
  have hbU : b ∈ Metric.ball b rb := Metric.mem_ball.mpr (by rw [dist_self]; exact hrb0)
  have hcU : c ∈ Metric.ball c rc := Metric.mem_ball.mpr (by rw [dist_self]; exact hrc0)
  have hsubaW : Metric.ball a ra ⊆ W := (subset_inter_iff.mp hsuba).1
  have hsubbW : Metric.ball b rb ⊆ W := (subset_inter_iff.mp hsubb).1
  have hsubcW : Metric.ball c rc ⊆ W := (subset_inter_iff.mp hsubc).1
  have hsubaO : Metric.ball a ra ⊆ Oab1 ∩ Oac1 := (subset_inter_iff.mp hsuba).2
  have hsubbO : Metric.ball b rb ⊆ Oab2 ∩ Obc1 := (subset_inter_iff.mp hsubb).2
  have hsubcO : Metric.ball c rc ⊆ Oac2 ∩ Obc2 := (subset_inter_iff.mp hsubc).2
  refine ⟨Metric.ball a ra, Metric.ball b rb, Metric.ball c rc, hcla, hclb, hclc,
    haU, hbU, hcU, hsubaW, hsubbW, hsubcW, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hdisjAB'.mono hsubaO hsubbO
  · exact hdisjAC'.mono hsubaO hsubcO
  · exact hdisjBC'.mono hsubbO hsubcO
  · exact Metric.ball_subset_ball (le_of_lt hraε)
  · exact Metric.ball_subset_ball (le_of_lt hrbε)
  · exact Metric.ball_subset_ball (le_of_lt hrcε)

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[perfectSpace_rat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma perfectSpace_rat : PerfectSpace ℚ := by
  refine ⟨preperfect_iff_nhds.mpr ?_⟩
  intro x _ U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hxy : (x : ℝ) < (x : ℝ) + ε := lt_add_of_pos_right (x : ℝ) hε
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hxy
  have hdist : dist r x < ε := by
    have hpos : (0 : ℝ) < (r : ℝ) - (x : ℝ) := sub_pos.mpr hr1
    have hlt : (r : ℝ) - (x : ℝ) < ε := by linarith
    have heq : dist r x = (r : ℝ) - (x : ℝ) := by
      rw [Rat.dist_eq, abs_of_pos hpos]
    rwa [heq]
  have hmem : r ∈ U := hball (Metric.mem_ball.mpr hdist)
  have hne : r ≠ x := by
    intro hcon
    have hcast : (r : ℝ) = (x : ℝ) := by rw [hcon]
    rw [hcast] at hr1
    exact lt_irrefl _ hr1
  exact ⟨r, ⟨hmem, mem_univ r⟩, hne⟩

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[initial_good](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma initial_good {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [PseudoMetricSpace X] [PseudoMetricSpace Y] [Nonempty X] [Nonempty Y] :
  IsGood ([⟨Set.univ, Set.univ, none, 0⟩] : List (Block X Y)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    rw [List.mem_singleton.mp hb]
    exact ⟨isClopen_univ, isClopen_univ, univ_nonempty, univ_nonempty⟩
  · intro b hb s t hpt
    rw [List.mem_singleton.mp hb] at hpt
    exact absurd hpt.symm (Option.some_ne_none _)
  · intro b1 hb1 b2 hb2 hne
    have h1 : b1 = ⟨Set.univ, Set.univ, none, 0⟩ := List.mem_singleton.mp hb1
    have h2 : b2 = ⟨Set.univ, Set.univ, none, 0⟩ := List.mem_singleton.mp hb2
    have hcon : b1 = b2 := by rw [h1, h2]
    exact absurd hcon hne
  · exact List.nodup_singleton _
  · constructor
    · intro x
      exact ⟨⟨Set.univ, Set.univ, none, 0⟩, List.mem_singleton.mpr rfl, mem_univ x⟩
    · intro y
      exact ⟨⟨Set.univ, Set.univ, none, 0⟩, List.mem_singleton.mpr rfl, mem_univ y⟩
  · intro b hb s t n hpt _
    rw [List.mem_singleton.mp hb] at hpt
    exact absurd hpt.symm (Option.some_ne_none _)

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[unique_block_X](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma unique_block_X {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [PseudoMetricSpace X] [PseudoMetricSpace Y] {l : List (Block X Y)}
  (hgood : IsGood l) {x : X} {b1 b2 : Block X Y} (h1 : b1 ∈ l) (hx1 : x ∈ b1.UX)
  (h2 : b2 ∈ l) (hx2 : x ∈ b2.UX) : b1 = b2 := by
  by_contra hne
  obtain ⟨_, _, hdisj, _, _, _⟩ := hgood
  obtain ⟨hdisjX, _⟩ := hdisj b1 h1 b2 h2 hne
  have hnot : x ∉ b2.UX := Set.disjoint_left.mp hdisjX hx1
  exact hnot hx2

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[unique_block_Y](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma unique_block_Y {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [PseudoMetricSpace X] [PseudoMetricSpace Y] {l : List (Block X Y)}
  (hgood : IsGood l) {y : Y} {b1 b2 : Block X Y} (h1 : b1 ∈ l) (hy1 : y ∈ b1.UY)
  (h2 : b2 ∈ l) (hy2 : y ∈ b2.UY) : b1 = b2 := by
  by_contra hne
  obtain ⟨_, _, hdisj, _, _, _⟩ := hgood
  obtain ⟨_, hdisjY⟩ := hdisj b1 h1 b2 h2 hne
  have hnot : y ∉ b2.UY := Set.disjoint_left.mp hdisjY hy1
  exact hnot hy2

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[matched_unique_X](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma matched_unique_X {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [PseudoMetricSpace X] [PseudoMetricSpace Y] {l : List (Block X Y)}
  (hgood : IsGood l) {x : X} {t1 t2 : Y} {b1 b2 : Block X Y} (h1 : b1 ∈ l)
  (hpt1 : b1.pt = some (x, t1)) (h2 : b2 ∈ l) (hpt2 : b2.pt = some (x, t2)) :
  t1 = t2 := by
  have hpts := hgood.2.1
  obtain ⟨hx1, _⟩ := hpts b1 h1 x t1 hpt1
  obtain ⟨hx2, _⟩ := hpts b2 h2 x t2 hpt2
  have hbeq : b1 = b2 := unique_block_X hgood h1 hx1 h2 hx2
  have hpt_eq : (x, t1) = (x, t2) := by
    have h1eq : b1.pt = some (x, t1) := hpt1
    have h2eq : b2.pt = some (x, t2) := hpt2
    rw [hbeq] at h1eq
    have hsome : some (x, t1) = some (x, t2) := h1eq.symm.trans h2eq
    exact Option.some_inj.mp hsome
  exact congrArg Prod.snd hpt_eq

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[matched_unique_Y](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma matched_unique_Y {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [PseudoMetricSpace X] [PseudoMetricSpace Y] {l : List (Block X Y)}
  (hgood : IsGood l) {y : Y} {s1 s2 : X} {b1 b2 : Block X Y} (h1 : b1 ∈ l)
  (hpt1 : b1.pt = some (s1, y)) (h2 : b2 ∈ l) (hpt2 : b2.pt = some (s2, y)) :
  s1 = s2 := by
  have hpts := hgood.2.1
  obtain ⟨_, hy1⟩ := hpts b1 h1 s1 y hpt1
  obtain ⟨_, hy2⟩ := hpts b2 h2 s2 y hpt2
  have hbeq : b1 = b2 := unique_block_Y hgood h1 hy1 h2 hy2
  have hpt_eq : (s1, y) = (s2, y) := by
    have h1eq : b1.pt = some (s1, y) := hpt1
    have h2eq : b2.pt = some (s2, y) := hpt2
    rw [hbeq] at h1eq
    have hsome : some (s1, y) = some (s2, y) := h1eq.symm.trans h2eq
    exact Option.some_inj.mp hsome
  exact congrArg Prod.fst hpt_eq

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[initial_goodS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma initial_goodS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] [Nonempty X] [Nonempty Y] :
  IsGoodS ({⟨Set.univ, Set.univ, none, 0⟩} : Set (Block X Y)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Set.finite_singleton _
  · intro b hb
    rw [Set.mem_singleton_iff.mp hb]
    exact ⟨isClopen_univ, isClopen_univ, univ_nonempty, univ_nonempty⟩
  · intro b hb p q hpt
    rw [Set.mem_singleton_iff.mp hb] at hpt
    exact absurd hpt.symm (Option.some_ne_none _)
  · intro b1 hb1 b2 hb2 hne
    have h1 : b1 = ⟨Set.univ, Set.univ, none, 0⟩ := Set.mem_singleton_iff.mp hb1
    have h2 : b2 = ⟨Set.univ, Set.univ, none, 0⟩ := Set.mem_singleton_iff.mp hb2
    have hcon : b1 = b2 := by rw [h1, h2]
    exact absurd hcon hne
  · constructor
    · intro x
      exact ⟨⟨Set.univ, Set.univ, none, 0⟩, Set.mem_singleton_iff.mpr rfl,
        mem_univ x⟩
    · intro y
      exact ⟨⟨Set.univ, Set.univ, none, 0⟩, Set.mem_singleton_iff.mpr rfl,
        mem_univ y⟩
  · intro b hb p q n hpt _
    rw [Set.mem_singleton_iff.mp hb] at hpt
    exact absurd hpt.symm (Option.some_ne_none _)

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[unique_block_XS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma unique_block_XS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] {s : Set (Block X Y)}
  (hgood : IsGoodS s) {x : X} {b1 b2 : Block X Y} (h1 : b1 ∈ s)
  (hx1 : x ∈ b1.UX) (h2 : b2 ∈ s) (hx2 : x ∈ b2.UX) : b1 = b2 := by
  by_contra hne
  obtain ⟨_, _, _, hdisj, _, _⟩ := hgood
  obtain ⟨hdisjX, _⟩ := hdisj b1 h1 b2 h2 hne
  have hnot : x ∉ b2.UX := Set.disjoint_left.mp hdisjX hx1
  exact hnot hx2

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[unique_block_YS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma unique_block_YS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] {s : Set (Block X Y)}
  (hgood : IsGoodS s) {y : Y} {b1 b2 : Block X Y} (h1 : b1 ∈ s)
  (hy1 : y ∈ b1.UY) (h2 : b2 ∈ s) (hy2 : y ∈ b2.UY) : b1 = b2 := by
  by_contra hne
  obtain ⟨_, _, _, hdisj, _, _⟩ := hgood
  obtain ⟨_, hdisjY⟩ := hdisj b1 h1 b2 h2 hne
  have hnot : y ∉ b2.UY := Set.disjoint_left.mp hdisjY hy1
  exact hnot hy2

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[matched_unique_XS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma matched_unique_XS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] {s : Set (Block X Y)}
  (hgood : IsGoodS s) {x : X} {t1 t2 : Y} {b1 b2 : Block X Y} (h1 : b1 ∈ s)
  (hpt1 : b1.pt = some (x, t1)) (h2 : b2 ∈ s) (hpt2 : b2.pt = some (x, t2)) :
  t1 = t2 := by
  have hpts := hgood.2.2.1
  obtain ⟨hx1, _⟩ := hpts b1 h1 x t1 hpt1
  obtain ⟨hx2, _⟩ := hpts b2 h2 x t2 hpt2
  have hbeq : b1 = b2 := unique_block_XS hgood h1 hx1 h2 hx2
  have hpt_eq : (x, t1) = (x, t2) := by
    have h1eq : b1.pt = some (x, t1) := hpt1
    have h2eq : b2.pt = some (x, t2) := hpt2
    rw [hbeq] at h1eq
    have hsome : some (x, t1) = some (x, t2) := h1eq.symm.trans h2eq
    exact Option.some_inj.mp hsome
  exact congrArg Prod.snd hpt_eq

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[matched_unique_YS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma matched_unique_YS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] {s : Set (Block X Y)}
  (hgood : IsGoodS s) {y : Y} {s1 s2 : X} {b1 b2 : Block X Y} (h1 : b1 ∈ s)
  (hpt1 : b1.pt = some (s1, y)) (h2 : b2 ∈ s) (hpt2 : b2.pt = some (s2, y)) :
  s1 = s2 := by
  have hpts := hgood.2.2.1
  obtain ⟨_, hy1⟩ := hpts b1 h1 s1 y hpt1
  obtain ⟨_, hy2⟩ := hpts b2 h2 s2 y hpt2
  have hbeq : b1 = b2 := unique_block_YS hgood h1 hy1 h2 hy2
  have hpt_eq : (s1, y) = (s2, y) := by
    have h1eq : b1.pt = some (s1, y) := hpt1
    have h2eq : b2.pt = some (s2, y) := hpt2
    rw [hbeq] at h1eq
    have hsome : some (s1, y) = some (s2, y) := h1eq.symm.trans h2eq
    exact Option.some_inj.mp hsome
  exact congrArg Prod.fst hpt_eq

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[isGood_replaceS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma isGood_replaceS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] {s : Set (Block X Y)}
  (hgood : IsGoodS s) {b : Block X Y} (hb : b ∈ s) {t : Set (Block X Y)}
  (hfin_t : t.Finite)
  (hclopen_t : ∀ c ∈ t, IsClopen c.UX ∧ IsClopen c.UY ∧ c.UX.Nonempty ∧ c.UY.Nonempty)
  (hpts_t : ∀ c ∈ t, ∀ p q, c.pt = some (p, q) → p ∈ c.UX ∧ q ∈ c.UY)
  (hdisj_t : ∀ c1 ∈ t, ∀ c2 ∈ t, c1 ≠ c2 → Disjoint c1.UX c2.UX ∧ Disjoint c1.UY c2.UY)
  (hsub_t : ∀ c ∈ t, c.UX ⊆ b.UX ∧ c.UY ⊆ b.UY)
  (hcoverX_t : ∀ x ∈ b.UX, ∃ c ∈ t, x ∈ c.UX)
  (hcoverY_t : ∀ y ∈ b.UY, ∃ c ∈ t, y ∈ c.UY)
  (hrad_t : ∀ c ∈ t, ∀ p q n, c.pt = some (p, q) → c.bound = n →
    c.UX ⊆ Metric.ball p (1 / ((n + 1 : ℕ) : ℝ)) ∧
    c.UY ⊆ Metric.ball q (1 / ((n + 1 : ℕ) : ℝ))) :
  IsGoodS (t ∪ (s \ {b})) ∧
  (∀ c' ∈ t ∪ (s \ {b}), ∃ c ∈ s, c'.UX ⊆ c.UX ∧ c'.UY ⊆ c.UY) := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hfin_t.union hgood.1.sdiff
    · intro c hc
      rw [Set.mem_union] at hc
      obtain hct | hcold := hc
      · exact hclopen_t c hct
      · have hcs : c ∈ s := (Set.mem_sdiff _).mp hcold |>.1
        exact hgood.2.1 c hcs
    · intro c hc p q hpt
      rw [Set.mem_union] at hc
      obtain hct | hcold := hc
      · exact hpts_t c hct p q hpt
      · have hcs : c ∈ s := (Set.mem_sdiff _).mp hcold |>.1
        exact hgood.2.2.1 c hcs p q hpt
    · intro b1 hb1 b2 hb2 hne
      rw [Set.mem_union] at hb1 hb2
      obtain h1t | h1old := hb1
      · rcases hb2 with h2t | h2old
        · exact hdisj_t b1 h1t b2 h2t hne
        · have h2s : b2 ∈ s := (Set.mem_sdiff _).mp h2old |>.1
          have h2ns : ¬b2 ∈ ({b} : Set (Block X Y)) :=
            (Set.mem_sdiff _).mp h2old |>.2
          have h2neb : b2 ≠ b := fun heq =>
            h2ns (Set.mem_singleton_iff.mpr heq)
          have hne_b2 : b ≠ b2 := Ne.symm h2neb
          obtain ⟨hdX, hdY⟩ := hgood.2.2.2.1 b hb b2 h2s hne_b2
          obtain ⟨hsX, hsY⟩ := hsub_t b1 h1t
          exact ⟨hdX.mono hsX Subset.rfl, hdY.mono hsY Subset.rfl⟩
      · rcases hb2 with h2t | h2old
        · have h1s : b1 ∈ s := (Set.mem_sdiff _).mp h1old |>.1
          have h1ns : ¬b1 ∈ ({b} : Set (Block X Y)) :=
            (Set.mem_sdiff _).mp h1old |>.2
          have h1neb : b1 ≠ b := fun heq =>
            h1ns (Set.mem_singleton_iff.mpr heq)
          obtain ⟨hdX, hdY⟩ := hgood.2.2.2.1 b1 h1s b hb h1neb
          obtain ⟨hsX, hsY⟩ := hsub_t b2 h2t
          exact ⟨hdX.mono Subset.rfl hsX, hdY.mono Subset.rfl hsY⟩
        · have h1s : b1 ∈ s := (Set.mem_sdiff _).mp h1old |>.1
          have h2s : b2 ∈ s := (Set.mem_sdiff _).mp h2old |>.1
          exact hgood.2.2.2.1 b1 h1s b2 h2s hne
    · constructor
      · intro x
        have hcoverX := hgood.2.2.2.2.1.1
        obtain ⟨c, hc, hxc⟩ := hcoverX x
        by_cases heq : c = b
        · rw [heq] at hxc
          obtain ⟨c', hc't, hxc'⟩ := hcoverX_t x hxc
          exact ⟨c', Set.mem_union_left _ hc't, hxc'⟩
        · have hcsdiff : c ∈ s \ {b} :=
          (Set.mem_sdiff _).mpr ⟨hc, fun hmem => heq (Set.mem_singleton_iff.mp hmem)⟩
          exact ⟨c, Set.mem_union_right _ hcsdiff, hxc⟩
      · intro y
        have hcoverY := hgood.2.2.2.2.1.2
        obtain ⟨c, hc, hyc⟩ := hcoverY y
        by_cases heq : c = b
        · rw [heq] at hyc
          obtain ⟨c', hc't, hyc'⟩ := hcoverY_t y hyc
          exact ⟨c', Set.mem_union_left _ hc't, hyc'⟩
        · have hcsdiff : c ∈ s \ {b} :=
          (Set.mem_sdiff _).mpr ⟨hc, fun hmem => heq (Set.mem_singleton_iff.mp hmem)⟩
          exact ⟨c, Set.mem_union_right _ hcsdiff, hyc⟩
    · intro c hc p q n hpt hbound
      rw [Set.mem_union] at hc
      obtain hct | hcold := hc
      · exact hrad_t c hct p q n hpt hbound
      · have hcs : c ∈ s := (Set.mem_sdiff _).mp hcold |>.1
        exact hgood.2.2.2.2.2 c hcs p q n hpt hbound
  · intro c' hc'
    rw [Set.mem_union] at hc'
    obtain hct | hcold := hc'
    · exact ⟨b, hb, hsub_t c' hct⟩
    · have hcs : c' ∈ s := (Set.mem_sdiff _).mp hcold |>.1
      exact ⟨c', hcs, Subset.rfl, Subset.rfl⟩

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[swap_pt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma Block.swap_pt {X Y : Type*} (b : Block X Y) (p : Y) (q : X) :
  (Block.swap b).pt = some (p, q) ↔ b.pt = some (q, p) := by
  cases hb : b.pt with
  | none =>
    constructor
    · intro h
      have h2 : b.pt.map Prod.swap = some (p, q) := h
      rw [hb, Option.map_none] at h2
      exact absurd h2.symm (Option.some_ne_none _)
    · intro h
      exact absurd h.symm (Option.some_ne_none _)
  | some v =>
    obtain ⟨a, c⟩ := v
    constructor
    · intro h
      have h2 : b.pt.map Prod.swap = some (p, q) := h
      rw [hb, Option.map_some] at h2
      have h3 : (c, a) = (p, q) := Option.some_inj.mp h2
      rw [Prod.mk.injEq] at h3
      obtain ⟨hcap, hacq⟩ := h3
      rw [hacq, hcap]
    · intro h
      have h3 : (a, c) = (q, p) := Option.some_inj.mp h
      rw [Prod.mk.injEq] at h3
      obtain ⟨haq, hcp⟩ := h3
      change b.pt.map Prod.swap = some (p, q)
      rw [hb, Option.map_some, Prod.swap_prod_mk, haq, hcp]

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[swap_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma Block.swap_swap {X Y : Type*} (b : Block X Y) :
  Block.swap (Block.swap b) = b := by
  cases b with
  | mk UX UY pt bound =>
    cases pt with
    | none => rfl
    | some v =>
      obtain ⟨a, c⟩ := v
      rfl

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[isGoodS_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma isGoodS_swap {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  {s : Set (Block X Y)} (hgood : IsGoodS s) : IsGoodS (Block.swap '' s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hgood.1.image _
  · intro c' hc'
    obtain ⟨c, hcs, rfl⟩ := (Set.mem_image _ _ _).mp hc'
    obtain ⟨hX, hY, hXn, hYn⟩ := hgood.2.1 c hcs
    exact ⟨hY, hX, hYn, hXn⟩
  · intro c' hc' p q hpt
    obtain ⟨c, hcs, rfl⟩ := (Set.mem_image _ _ _).mp hc'
    have hptc : c.pt = some (q, p) := (Block.swap_pt c p q).mp hpt
    obtain ⟨hq, hp⟩ := hgood.2.2.1 c hcs q p hptc
    exact ⟨hp, hq⟩
  · intro b1 hb1 b2 hb2 hne
    obtain ⟨d1, hd1, rfl⟩ := (Set.mem_image _ _ _).mp hb1
    obtain ⟨d2, hd2, rfl⟩ := (Set.mem_image _ _ _).mp hb2
    have hne' : d1 ≠ d2 := fun heq => hne (by rw [heq])
    obtain ⟨hdX, hdY⟩ := hgood.2.2.2.1 d1 hd1 d2 hd2 hne'
    exact ⟨hdY, hdX⟩
  · constructor
    · intro y
      obtain ⟨c, hc, hyc⟩ := hgood.2.2.2.2.1.2 y
      exact ⟨Block.swap c, Set.mem_image_of_mem _ hc, hyc⟩
    · intro x
      obtain ⟨c, hc, hxc⟩ := hgood.2.2.2.2.1.1 x
      exact ⟨Block.swap c, Set.mem_image_of_mem _ hc, hxc⟩
  · intro c' hc' p q n hpt hbound
    obtain ⟨c, hcs, rfl⟩ := (Set.mem_image _ _ _).mp hc'
    have hptc : c.pt = some (q, p) := (Block.swap_pt c p q).mp hpt
    have hboundc : c.bound = n := hbound
    obtain ⟨hX, hY⟩ := hgood.2.2.2.2.2 c hcs q p n hptc hboundc
    exact ⟨hY, hX⟩

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[exists_forwardS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma exists_forwardS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] [T2Space X] [T2Space Y]
  [Countable X] [Countable Y] [PerfectSpace X] [PerfectSpace Y]
  {s : Set (Block X Y)} (hgood : IsGoodS s) (xstar : X) (N : ℕ) :
  ∃ s' : Set (Block X Y), IsGoodS s' ∧
    (∀ c' ∈ s', ∃ c ∈ s, c'.UX ⊆ c.UX ∧ c'.UY ⊆ c.UY) ∧
    (∀ b ∈ s, ∀ p q, b.pt = some (p, q) → ∃ b' ∈ s', b'.pt = some (p, q)) ∧
    (∃ t, ∃ b' ∈ s', b'.pt = some (xstar, t)) ∧
    (∀ b' ∈ s', ∀ p q, b'.pt = some (p, q) → b' ∈ s ∨ b'.bound = N) := by
  by_cases hmatched : ∃ b ∈ s, ∃ t, b.pt = some (xstar, t)
  · obtain ⟨b0, hb0, t0, hpt0⟩ := hmatched
    exact ⟨s, hgood, fun c' hc' => ⟨c', hc', Subset.rfl, Subset.rfl⟩,
      fun b hb p q hpt => ⟨b, hb, hpt⟩, ⟨t0, b0, hb0, hpt0⟩,
      fun b' hb' _ _ _ => Or.inl hb'⟩
  · have hcoverX := hgood.2.2.2.2.1.1
    obtain ⟨b, hb, hxb⟩ := hcoverX xstar
    cases hbpt : b.pt
    · have hclopen := hgood.2.1 b hb
      obtain ⟨hbUX_clopen, hbUY_clopen, hbUX_ne, hbUY_ne⟩ := hclopen
      have hUX_inf : b.UX.Infinite :=
        infinite_of_nonempty_clopen hbUX_ne hbUX_clopen
      have hUY_inf : b.UY.Infinite :=
        infinite_of_nonempty_clopen hbUY_ne hbUY_clopen
      obtain ⟨ystar, hystar⟩ := hbUY_ne
      obtain ⟨z, hz_mem, hz_nmem⟩ :=
        hUX_inf.exists_notMem_finite (Set.finite_singleton xstar)
      have hz_ne : z ≠ xstar := fun heq =>
        hz_nmem (Set.mem_singleton_iff.mpr heq)
      obtain ⟨w, hw_mem, hw_nmem⟩ :=
        hUY_inf.exists_notMem_finite (Set.finite_singleton ystar)
      have hw_ne : w ≠ ystar := fun heq =>
        hw_nmem (Set.mem_singleton_iff.mpr heq)
      have hε : (0 : ℝ) < 1 / ((N + 1 : ℕ) : ℝ) :=
        one_div_pos.mpr (Nat.cast_pos.mpr (by omega))
      have hxz : xstar ≠ z := Ne.symm hz_ne
      have hyw : ystar ≠ w := Ne.symm hw_ne
      obtain ⟨Bx, Bz, hBx_cl, hBz_cl, hxBx, hzBz, hBxW, hBzW, hdisjX, hBx_ball,
        _⟩ := exists_disjoint_clopen hbUX_clopen hxb hz_mem hxz hε
      obtain ⟨By, Bw, hBy_cl, hBw_cl, hyBy, hwBw, hByW, hBwW, hdisjY, hBy_ball,
        _⟩ := exists_disjoint_clopen hbUY_clopen hystar hw_mem hyw hε
      set LX : Set X := b.UX \ Bx with hLX
      set LY : Set Y := b.UY \ By with hLY
      have hBz_sub : Bz ⊆ LX := fun y hy =>
        (Set.mem_sdiff _).mpr ⟨hBzW hy, Set.disjoint_right.mp hdisjX hy⟩
      have hBw_sub : Bw ⊆ LY := fun y hy =>
        (Set.mem_sdiff _).mpr ⟨hBwW hy, Set.disjoint_right.mp hdisjY hy⟩
      have hLX_cl : IsClopen LX := hbUX_clopen.diff hBx_cl
      have hLY_cl : IsClopen LY := hbUY_clopen.diff hBy_cl
      have hLX_ne : LX.Nonempty := ⟨z, hBz_sub hzBz⟩
      have hLY_ne : LY.Nonempty := ⟨w, hBw_sub hwBw⟩
      set c1 : Block X Y := ⟨Bx, By, some (xstar, ystar), N⟩ with hc1
      set c2 : Block X Y := ⟨LX, LY, none, 0⟩ with hc2
      set t : Set (Block X Y) := {c1, c2} with ht
      have hfin_t : t.Finite := by
        rw [ht]
        exact (Set.finite_singleton c2).insert c1
      have hclopen_t : ∀ c ∈ t,
        IsClopen c.UX ∧ IsClopen c.UY ∧ c.UX.Nonempty ∧ c.UY.Nonempty := by
        intro c hc
        rw [ht, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        obtain rfl | rfl := hc
        · rw [hc1]
          exact ⟨hBx_cl, hBy_cl, ⟨xstar, hxBx⟩, ⟨ystar, hyBy⟩⟩
        · rw [hc2]
          exact ⟨hLX_cl, hLY_cl, hLX_ne, hLY_ne⟩
      have hpts_t : ∀ c ∈ t, ∀ p q, c.pt = some (p, q) → p ∈ c.UX ∧ q ∈ c.UY := by
        intro c hc p q hpt
        rw [ht, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        obtain rfl | rfl := hc
        · rw [hc1] at hpt
          have hpair : (xstar, ystar) = (p, q) := Option.some_inj.mp hpt
          rw [Prod.mk.injEq] at hpair
          obtain ⟨rfl, rfl⟩ := hpair
          rw [hc1]
          exact ⟨hxBx, hyBy⟩
        · rw [hc2] at hpt
          exact absurd hpt.symm (Option.some_ne_none _)
      have hdisj_t : ∀ c1' ∈ t, ∀ c2' ∈ t, c1' ≠ c2' →
        Disjoint c1'.UX c2'.UX ∧ Disjoint c1'.UY c2'.UY := by
        intro c1' hc1' c2' hc2' hne
        rw [ht, Set.mem_insert_iff, Set.mem_singleton_iff] at hc1' hc2'
        obtain rfl | rfl <;> rcases hc2' with rfl | rfl := hc1'
        · exact absurd rfl hne
        · rw [hc1, hc2]
          have hX : Disjoint Bx LX := by
            rw [hLX]
            exact Set.disjoint_left.mpr fun a ha1 ha2 =>
              (Set.mem_sdiff _).mp ha2 |>.2 ha1
          have hY : Disjoint By LY := by
            rw [hLY]
            exact Set.disjoint_left.mpr fun a ha1 ha2 =>
              (Set.mem_sdiff _).mp ha2 |>.2 ha1
          exact ⟨hX, hY⟩
        · rw [hc1, hc2]
          have hX : Disjoint LX Bx := by
            rw [hLX]
            exact Set.disjoint_left.mpr fun a ha1 ha2 =>
              (Set.mem_sdiff _).mp ha1 |>.2 ha2
          have hY : Disjoint LY By := by
            rw [hLY]
            exact Set.disjoint_left.mpr fun a ha1 ha2 =>
              (Set.mem_sdiff _).mp ha1 |>.2 ha2
          exact ⟨hX, hY⟩
        · exact absurd rfl hne
      have hsub_t : ∀ c ∈ t, c.UX ⊆ b.UX ∧ c.UY ⊆ b.UY := by
        intro c hc
        rw [ht, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        obtain rfl | rfl := hc
        · rw [hc1]
          exact ⟨hBxW, hByW⟩
        · rw [hc2, hLX, hLY]
          exact ⟨Set.sdiff_subset, Set.sdiff_subset⟩
      have hcoverX_t : ∀ x ∈ b.UX, ∃ c ∈ t, x ∈ c.UX := by
        intro x hx
        by_cases hxBx : x ∈ Bx
        · exact ⟨c1, Set.mem_insert c1 _, by rw [hc1]; exact hxBx⟩
        · have hxLX : x ∈ LX := (Set.mem_sdiff _).mpr ⟨hx, hxBx⟩
          have hc2t : c2 ∈ t := by
            rw [ht]
            exact Set.mem_insert_of_mem _
              (Set.mem_singleton_iff.mpr rfl)
          exact ⟨c2, hc2t, by rw [hc2]; exact hxLX⟩
      have hcoverY_t : ∀ y ∈ b.UY, ∃ c ∈ t, y ∈ c.UY := by
        intro y hy
        by_cases hyBy : y ∈ By
        · exact ⟨c1, Set.mem_insert c1 _, by rw [hc1]; exact hyBy⟩
        · have hyLY : y ∈ LY := (Set.mem_sdiff _).mpr ⟨hy, hyBy⟩
          have hc2t : c2 ∈ t := by
            rw [ht]
            exact Set.mem_insert_of_mem _
              (Set.mem_singleton_iff.mpr rfl)
          exact ⟨c2, hc2t, by rw [hc2]; exact hyLY⟩
      have hrad_t : ∀ c ∈ t, ∀ p q n, c.pt = some (p, q) → c.bound = n →
        c.UX ⊆ Metric.ball p (1 / ((n + 1 : ℕ) : ℝ)) ∧
        c.UY ⊆ Metric.ball q (1 / ((n + 1 : ℕ) : ℝ)) := by
        intro c hc p q n hpt hbound
        rw [ht, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        obtain rfl | rfl := hc
        · rw [hc1] at hpt hbound ⊢
          simp only at hbound
          subst hbound
          have hpair : (xstar, ystar) = (p, q) := Option.some_inj.mp hpt
          rw [Prod.mk.injEq] at hpair
          obtain ⟨rfl, rfl⟩ := hpair
          exact ⟨hBx_ball, hBy_ball⟩
        · rw [hc2] at hpt
          exact absurd hpt.symm (Option.some_ne_none _)
      obtain ⟨hgood', hrefine⟩ := isGood_replaceS hgood hb hfin_t hclopen_t
        hpts_t hdisj_t hsub_t hcoverX_t hcoverY_t hrad_t
      have hpersist : ∀ b0 ∈ s, ∀ p q, b0.pt = some (p, q) →
        ∃ b' ∈ t ∪ (s \ {b}), b'.pt = some (p, q) := by
        intro b0 hb0 p q hpt0
        have hne : b0 ≠ b := fun heq => by
          rw [heq] at hpt0
          rw [hbpt] at hpt0
          exact Option.some_ne_none _ hpt0.symm
        have hmem : b0 ∈ s \ {b} := (Set.mem_sdiff _).mpr
          ⟨hb0, fun hmem => hne (Set.mem_singleton_iff.mp hmem)⟩
        exact ⟨b0, Set.mem_union_right _ hmem, hpt0⟩
      have hc1t : c1 ∈ t := by
        rw [ht]
        exact Set.mem_insert c1 _
      have hc1s' : c1 ∈ t ∪ (s \ {b}) := Set.mem_union_left _ hc1t
      have hpt1 : c1.pt = some (xstar, ystar) := by rw [hc1]
      have hbnd_new : ∀ b' ∈ t ∪ (s \ {b}), ∀ p q, b'.pt = some (p, q) →
        b' ∈ s ∨ b'.bound = N := by
        intro b' hb' p q hpt
        rw [Set.mem_union] at hb'
        obtain hct | hcold := hb'
        · rw [ht, Set.mem_insert_iff, Set.mem_singleton_iff] at hct
          obtain rfl | rfl := hct
          · right
            rw [hc1]
          · rw [hc2] at hpt
            exact absurd hpt.symm (Option.some_ne_none _)
        · left
          exact (Set.mem_sdiff _).mp hcold |>.1
      exact ⟨t ∪ (s \ {b}), hgood', hrefine, hpersist, ⟨ystar, c1, hc1s', hpt1⟩,
        hbnd_new⟩
    · rename_i val
      obtain ⟨s0, t0⟩ := val
      have hclopen := hgood.2.1 b hb
      obtain ⟨hbUX_clopen, hbUY_clopen, hbUX_ne, hbUY_ne⟩ := hclopen
      have hpts := hgood.2.2.1 b hb s0 t0 hbpt
      obtain ⟨hs0X, ht0Y⟩ := hpts
      have hxs0 : xstar ≠ s0 := fun heq => hmatched ⟨b, hb, t0, by rw [heq, hbpt]⟩
      have hUX_inf : b.UX.Infinite :=
        infinite_of_nonempty_clopen hbUX_ne hbUX_clopen
      have hUY_inf : b.UY.Infinite :=
        infinite_of_nonempty_clopen hbUY_ne hbUY_clopen
      obtain ⟨ystar, hystar_mem, hystar_nmem⟩ :=
        hUY_inf.exists_notMem_finite (Set.finite_singleton t0)
      have hy_ne : ystar ≠ t0 := fun heq =>
        hystar_nmem (Set.mem_singleton_iff.mpr heq)
      obtain ⟨z, hz_mem, hz_nmem⟩ := hUX_inf.exists_notMem_finite
        (Set.finite_singleton s0 |>.insert xstar)
      have hz_ne_x : z ≠ xstar := fun heq =>
        hz_nmem (Set.mem_insert_iff.mpr (Or.inl heq))
      have hz_ne_s : z ≠ s0 := fun heq =>
        hz_nmem (Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_singleton_iff.mpr heq)))
      obtain ⟨w, hw_mem, hw_nmem⟩ := hUY_inf.exists_notMem_finite
        (Set.finite_singleton t0 |>.insert ystar)
      have hw_ne_y : w ≠ ystar := fun heq =>
        hw_nmem (Set.mem_insert_iff.mpr (Or.inl heq))
      have hw_ne_t : w ≠ t0 := fun heq =>
        hw_nmem (Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_singleton_iff.mpr heq)))
      have hε : (0 : ℝ) < 1 / ((N + 1 : ℕ) : ℝ) :=
        one_div_pos.mpr (Nat.cast_pos.mpr (by omega))
      have hsx : s0 ≠ xstar := Ne.symm hxs0
      have hsz : s0 ≠ z := Ne.symm hz_ne_s
      have hxz : xstar ≠ z := Ne.symm hz_ne_x
      have hty : t0 ≠ ystar := Ne.symm hy_ne
      have htw : t0 ≠ w := Ne.symm hw_ne_t
      have hyw : ystar ≠ w := Ne.symm hw_ne_y
      obtain ⟨Bs, Bx, Bz, hBs_cl, hBx_cl, hBz_cl, hsBs, hxBx, hzBz, hBsW, hBxW,
        hBzW, hdisjSX, hdisjSZ, hdisjXZ, hBs_ball, hBx_ball, _⟩ :=
        exists_three_disjoint_clopen hbUX_clopen hs0X hxb hz_mem hsx hsz hxz hε
      obtain ⟨Bt, By, Bw, hBt_cl, hBy_cl, hBw_cl, htBt, hyBy, hwBw, hBtW, hByW,
        hBwW, hdisjTY, hdisjTW, hdisjYW, hBt_ball, hBy_ball, _⟩ :=
        exists_three_disjoint_clopen hbUY_clopen ht0Y hystar_mem hw_mem hty htw hyw hε
      set LX : Set X := b.UX \ (Bs ∪ Bx) with hLX
      set LY : Set Y := b.UY \ (Bt ∪ By) with hLY
      have hBz_sub : Bz ⊆ LX := by
        intro y hy
        have hyW : y ∈ b.UX := hBzW hy
        have hyBs : y ∉ Bs := Set.disjoint_right.mp hdisjSZ hy
        have hyBx : y ∉ Bx := Set.disjoint_right.mp hdisjXZ hy
        have hyn : ¬y ∈ Bs ∪ Bx := by
          rw [Set.mem_union]
          exact fun h => h.elim hyBs hyBx
        exact (Set.mem_sdiff _).mpr ⟨hyW, hyn⟩
      have hBw_sub : Bw ⊆ LY := by
        intro y hy
        have hyW : y ∈ b.UY := hBwW hy
        have hyBt : y ∉ Bt := Set.disjoint_right.mp hdisjTW hy
        have hyBy : y ∉ By := Set.disjoint_right.mp hdisjYW hy
        have hyn : ¬y ∈ Bt ∪ By := by
          rw [Set.mem_union]
          exact fun h => h.elim hyBt hyBy
        exact (Set.mem_sdiff _).mpr ⟨hyW, hyn⟩
      have hLX_cl : IsClopen LX := hbUX_clopen.diff (hBs_cl.union hBx_cl)
      have hLY_cl : IsClopen LY := hbUY_clopen.diff (hBt_cl.union hBy_cl)
      have hLX_ne : LX.Nonempty := ⟨z, hBz_sub hzBz⟩
      have hLY_ne : LY.Nonempty := ⟨w, hBw_sub hwBw⟩
      set c1 : Block X Y := ⟨Bs, Bt, some (s0, t0), N⟩ with hc1
      set c2 : Block X Y := ⟨Bx, By, some (xstar, ystar), N⟩ with hc2
      set c3 : Block X Y := ⟨LX, LY, none, 0⟩ with hc3
      set t : Set (Block X Y) := {c1, c2, c3} with ht
      have hfin_t : t.Finite := by
        rw [ht]
        exact ((Set.finite_singleton c3).insert c2).insert c1
      have hclopen_t : ∀ c ∈ t,
        IsClopen c.UX ∧ IsClopen c.UY ∧ c.UX.Nonempty ∧ c.UY.Nonempty := by
        intro c hc
        rw [ht] at hc
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        obtain rfl | rfl | rfl := hc
        · rw [hc1]
          exact ⟨hBs_cl, hBt_cl, ⟨s0, hsBs⟩, ⟨t0, htBt⟩⟩
        · rw [hc2]
          exact ⟨hBx_cl, hBy_cl, ⟨xstar, hxBx⟩, ⟨ystar, hyBy⟩⟩
        · rw [hc3]
          exact ⟨hLX_cl, hLY_cl, hLX_ne, hLY_ne⟩
      have hpts_t : ∀ c ∈ t, ∀ p q, c.pt = some (p, q) → p ∈ c.UX ∧ q ∈ c.UY := by
        intro c hc p q hpt
        rw [ht] at hc
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        obtain rfl | rfl | rfl := hc
        · rw [hc1] at hpt
          have hpair : (s0, t0) = (p, q) := Option.some_inj.mp hpt
          rw [Prod.mk.injEq] at hpair
          obtain ⟨rfl, rfl⟩ := hpair
          rw [hc1]
          exact ⟨hsBs, htBt⟩
        · rw [hc2] at hpt
          have hpair : (xstar, ystar) = (p, q) := Option.some_inj.mp hpt
          rw [Prod.mk.injEq] at hpair
          obtain ⟨rfl, rfl⟩ := hpair
          rw [hc2]
          exact ⟨hxBx, hyBy⟩
        · rw [hc3] at hpt
          exact absurd hpt.symm (Option.some_ne_none _)
      have hBsLX : Disjoint Bs LX := by
        rw [hLX]
        exact Set.disjoint_left.mpr fun a ha1 ha2 =>
          ((Set.mem_sdiff _).mp ha2 |>.2) (Set.mem_union_left _ ha1)
      have hBxLX : Disjoint Bx LX := by
        rw [hLX]
        exact Set.disjoint_left.mpr fun a ha1 ha2 =>
          ((Set.mem_sdiff _).mp ha2 |>.2) (Set.mem_union_right _ ha1)
      have hBtLY : Disjoint Bt LY := by
        rw [hLY]
        exact Set.disjoint_left.mpr fun a ha1 ha2 =>
          ((Set.mem_sdiff _).mp ha2 |>.2) (Set.mem_union_left _ ha1)
      have hByLY : Disjoint By LY := by
        rw [hLY]
        exact Set.disjoint_left.mpr fun a ha1 ha2 =>
          ((Set.mem_sdiff _).mp ha2 |>.2) (Set.mem_union_right _ ha1)
      have hdisj_t : ∀ c1' ∈ t, ∀ c2' ∈ t, c1' ≠ c2' →
        Disjoint c1'.UX c2'.UX ∧ Disjoint c1'.UY c2'.UY := by
        intro c1' hc1' c2' hc2' hne
        rw [ht] at hc1' hc2'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc1' hc2'
        obtain rfl | rfl | rfl <;> rcases hc2' with rfl | rfl | rfl := hc1'
        · exact absurd rfl hne
        · rw [hc1, hc2]
          exact ⟨hdisjSX, hdisjTY⟩
        · rw [hc1, hc3]
          exact ⟨hBsLX, hBtLY⟩
        · rw [hc1, hc2]
          exact ⟨hdisjSX.symm, hdisjTY.symm⟩
        · exact absurd rfl hne
        · rw [hc2, hc3]
          exact ⟨hBxLX, hByLY⟩
        · rw [hc1, hc3]
          exact ⟨hBsLX.symm, hBtLY.symm⟩
        · rw [hc2, hc3]
          exact ⟨hBxLX.symm, hByLY.symm⟩
        · exact absurd rfl hne
      have hsub_t : ∀ c ∈ t, c.UX ⊆ b.UX ∧ c.UY ⊆ b.UY := by
        intro c hc
        rw [ht] at hc
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        obtain rfl | rfl | rfl := hc
        · rw [hc1]
          exact ⟨hBsW, hBtW⟩
        · rw [hc2]
          exact ⟨hBxW, hByW⟩
        · rw [hc3, hLX, hLY]
          exact ⟨Set.sdiff_subset, Set.sdiff_subset⟩
      have hcoverX_t : ∀ x ∈ b.UX, ∃ c ∈ t, x ∈ c.UX := by
        intro x hx
        by_cases hxBs : x ∈ Bs
        · exact ⟨c1, by rw [ht]; exact Set.mem_insert c1 _, by rw [hc1]; exact hxBs⟩
        · by_cases hxBx : x ∈ Bx
          · have hc2t : c2 ∈ t := by
            rw [ht]
            exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
            exact ⟨c2, hc2t, by rw [hc2]; exact hxBx⟩
          · have hxLX : x ∈ LX := by
            rw [hLX]
            exact (Set.mem_sdiff _).mpr ⟨hx, by
              rw [Set.mem_union]
              exact fun h => h.elim hxBs hxBx⟩
            have hc3t : c3 ∈ t := by
              rw [ht]
              exact Set.mem_insert_of_mem _
                (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr rfl))
            exact ⟨c3, hc3t, by rw [hc3]; exact hxLX⟩
      have hcoverY_t : ∀ y ∈ b.UY, ∃ c ∈ t, y ∈ c.UY := by
        intro y hy
        by_cases hyBt : y ∈ Bt
        · exact ⟨c1, by rw [ht]; exact Set.mem_insert c1 _, by rw [hc1]; exact hyBt⟩
        · by_cases hyBy : y ∈ By
          · have hc2t : c2 ∈ t := by
            rw [ht]
            exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
            exact ⟨c2, hc2t, by rw [hc2]; exact hyBy⟩
          · have hyLY : y ∈ LY := by
            rw [hLY]
            exact (Set.mem_sdiff _).mpr ⟨hy, by
              rw [Set.mem_union]
              exact fun h => h.elim hyBt hyBy⟩
            have hc3t : c3 ∈ t := by
              rw [ht]
              exact Set.mem_insert_of_mem _
                (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr rfl))
            exact ⟨c3, hc3t, by rw [hc3]; exact hyLY⟩
      have hrad_t : ∀ c ∈ t, ∀ p q n, c.pt = some (p, q) → c.bound = n →
        c.UX ⊆ Metric.ball p (1 / ((n + 1 : ℕ) : ℝ)) ∧
        c.UY ⊆ Metric.ball q (1 / ((n + 1 : ℕ) : ℝ)) := by
        intro c hc p q n hpt hbound
        rw [ht] at hc
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        obtain rfl | rfl | rfl := hc
        · rw [hc1] at hpt hbound ⊢
          simp only at hbound
          subst hbound
          have hpair : (s0, t0) = (p, q) := Option.some_inj.mp hpt
          rw [Prod.mk.injEq] at hpair
          obtain ⟨rfl, rfl⟩ := hpair
          exact ⟨hBs_ball, hBt_ball⟩
        · rw [hc2] at hpt hbound ⊢
          simp only at hbound
          subst hbound
          have hpair : (xstar, ystar) = (p, q) := Option.some_inj.mp hpt
          rw [Prod.mk.injEq] at hpair
          obtain ⟨rfl, rfl⟩ := hpair
          exact ⟨hBx_ball, hBy_ball⟩
        · rw [hc3] at hpt
          exact absurd hpt.symm (Option.some_ne_none _)
      obtain ⟨hgood', hrefine⟩ := isGood_replaceS hgood hb hfin_t hclopen_t
        hpts_t hdisj_t hsub_t hcoverX_t hcoverY_t hrad_t
      have hpersist : ∀ b0 ∈ s, ∀ p q, b0.pt = some (p, q) →
        ∃ b' ∈ t ∪ (s \ {b}), b'.pt = some (p, q) := by
        intro b0 hb0 p q hpt0
        by_cases heq : b0 = b
        · subst heq
          rw [hbpt] at hpt0
          have hpair : (s0, t0) = (p, q) := Option.some_inj.mp hpt0
          rw [Prod.mk.injEq] at hpair
          obtain ⟨rfl, rfl⟩ := hpair
          have hc1t : c1 ∈ t := by
            rw [ht]
            exact Set.mem_insert c1 _
          exact ⟨c1, Set.mem_union_left _ hc1t, by rw [hc1]⟩
        · have hmem : b0 ∈ s \ {b} := (Set.mem_sdiff _).mpr
          ⟨hb0, fun hmem => heq (Set.mem_singleton_iff.mp hmem)⟩
          exact ⟨b0, Set.mem_union_right _ hmem, hpt0⟩
      have hc2t : c2 ∈ t := by
        rw [ht]
        exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      have hc2s' : c2 ∈ t ∪ (s \ {b}) := Set.mem_union_left _ hc2t
      have hpt2 : c2.pt = some (xstar, ystar) := by rw [hc2]
      have hbnd_new : ∀ b' ∈ t ∪ (s \ {b}), ∀ p q, b'.pt = some (p, q) →
        b' ∈ s ∨ b'.bound = N := by
        intro b' hb' p q hpt
        rw [Set.mem_union] at hb'
        obtain hct | hcold := hb'
        · rw [ht] at hct
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hct
          obtain rfl | rfl | rfl := hct
          · right
            rw [hc1]
          · right
            rw [hc2]
          · rw [hc3] at hpt
            exact absurd hpt.symm (Option.some_ne_none _)
        · left
          exact (Set.mem_sdiff _).mp hcold |>.1
      exact ⟨t ∪ (s \ {b}), hgood', hrefine, hpersist, ⟨ystar, c2, hc2s', hpt2⟩,
        hbnd_new⟩

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[exists_backwardS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma exists_backwardS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] [T2Space X] [T2Space Y]
  [Countable X] [Countable Y] [PerfectSpace X] [PerfectSpace Y]
  {s : Set (Block X Y)} (hgood : IsGoodS s) (ystar : Y) (N : ℕ) :
  ∃ s' : Set (Block X Y), IsGoodS s' ∧
    (∀ c' ∈ s', ∃ c ∈ s, c'.UX ⊆ c.UX ∧ c'.UY ⊆ c.UY) ∧
    (∀ b ∈ s, ∀ p q, b.pt = some (p, q) → ∃ b' ∈ s', b'.pt = some (p, q)) ∧
    (∃ s_, ∃ b' ∈ s', b'.pt = some (s_, ystar)) ∧
    (∀ b' ∈ s', ∀ p q, b'.pt = some (p, q) → b' ∈ s ∨ b'.bound = N) := by
  have hgoodSwap : IsGoodS (Block.swap '' s) := isGoodS_swap hgood
  obtain ⟨t', hgood', href', hper', hmatch', hbnd'⟩ :=
    exists_forwardS hgoodSwap ystar N
  obtain ⟨s_, d', hd', hpt'⟩ := hmatch'
  refine ⟨Block.swap '' t', isGoodS_swap hgood', ?_, ?_, ?_, ?_⟩
  · intro c' hc'
    obtain ⟨d, hd, rfl⟩ := (Set.mem_image _ _ _).mp hc'
    obtain ⟨d0, hd0, hX0, hY0⟩ := href' d hd
    obtain ⟨c, hc, rfl⟩ := (Set.mem_image _ _ _).mp hd0
    exact ⟨c, hc, hY0, hX0⟩
  · intro b hb p q hpt
    have hbSwap : Block.swap b ∈ Block.swap '' s := Set.mem_image_of_mem _ hb
    have hptSwap : (Block.swap b).pt = some (q, p) := (Block.swap_pt b q p).mpr hpt
    obtain ⟨d', hd', hptd'⟩ := hper' (Block.swap b) hbSwap q p hptSwap
    exact ⟨Block.swap d', Set.mem_image_of_mem _ hd',
      (Block.swap_pt d' p q).mpr hptd'⟩
  · exact ⟨s_, Block.swap d', Set.mem_image_of_mem _ hd',
    (Block.swap_pt d' s_ ystar).mpr hpt'⟩
  · intro b' hb' p q hpt
    obtain ⟨d, hd, rfl⟩ := (Set.mem_image _ _ _).mp hb'
    have hptd : d.pt = some (q, p) := (Block.swap_pt d p q).mp hpt
    obtain h | h := hbnd' d hd q p hptd
    · obtain ⟨c, hc, rfl⟩ := (Set.mem_image _ _ _).mp h
      left
      rwa [Block.swap_swap]
    · right
      exact h

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[exists_stepS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma exists_stepS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] [T2Space X] [T2Space Y]
  [Countable X] [Countable Y] [PerfectSpace X] [PerfectSpace Y]
  {s : Set (Block X Y)} (hgood : IsGoodS s) (u : X) (v : Y) (N : ℕ) :
  ∃ s' : Set (Block X Y), IsGoodS s' ∧
    (∀ c' ∈ s', ∃ c ∈ s, c'.UX ⊆ c.UX ∧ c'.UY ⊆ c.UY) ∧
    (∀ b ∈ s, ∀ p q, b.pt = some (p, q) → ∃ b' ∈ s', b'.pt = some (p, q)) ∧
    (∃ t, ∃ b' ∈ s', b'.pt = some (u, t)) ∧
    (∃ s_, ∃ b' ∈ s', b'.pt = some (s_, v)) ∧
    (∀ b' ∈ s', ∀ p q, b'.pt = some (p, q) → b' ∈ s ∨ b'.bound = N) := by
  obtain ⟨s1, hgood1, href1, hper1, hmatch1, hbnd1⟩ :=
    exists_forwardS hgood u N
  obtain ⟨t1, b1, hb1, hpt1⟩ := hmatch1
  obtain ⟨s2, hgood2, href2, hper2, hmatch2, hbnd2⟩ :=
    exists_backwardS hgood1 v N
  refine ⟨s2, hgood2, ?_, ?_, ?_, hmatch2, ?_⟩
  · intro c' hc'
    obtain ⟨c1, hc1, hX1, hY1⟩ := href2 c' hc'
    obtain ⟨c, hc, hX, hY⟩ := href1 c1 hc1
    exact ⟨c, hc, hX1.trans hX, hY1.trans hY⟩
  · intro b hb p q hpt
    obtain ⟨b1', hb1', hpt1'⟩ := hper1 b hb p q hpt
    exact hper2 b1' hb1' p q hpt1'
  · obtain ⟨b1', hb1', hpt1'⟩ := hper2 b1 hb1 _ _ hpt1
    exact ⟨t1, b1', hb1', hpt1'⟩
  · intro b' hb' p q hpt
    obtain h | h := hbnd2 b' hb' p q hpt
    · rcases hbnd1 b' h p q hpt with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · exact Or.inr h

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[refine_le_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma refine_le_of_step {X Y : Type*} (S : ℕ → Set (Block X Y))
  (href : ∀ k, ∀ c' ∈ S (k + 1), ∃ c ∈ S k, c'.UX ⊆ c.UX ∧ c'.UY ⊆ c.UY) :
  ∀ j k, j ≤ k → ∀ c' ∈ S k, ∃ c ∈ S j, c'.UX ⊆ c.UX ∧ c'.UY ⊆ c.UY := by
  intro j k
  induction k with
  | zero =>
    intro hjk c' hc'
    have hj0 : j = 0 := by omega
    subst hj0
    exact ⟨c', hc', Subset.rfl, Subset.rfl⟩
  | succ k IH =>
    intro hjk c' hc'
    obtain hlt | heq := lt_or_eq_of_le hjk
    · have hle : j ≤ k := by omega
      obtain ⟨c1, hc1, hX1, hY1⟩ := href k c' hc'
      obtain ⟨c, hc, hX, hY⟩ := IH hle c1 hc1
      exact ⟨c, hc, hX1.trans hX, hY1.trans hY⟩
    · subst heq
      exact ⟨c', hc', Subset.rfl, Subset.rfl⟩

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[persist_le_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma persist_le_of_step {X Y : Type*} (S : ℕ → Set (Block X Y))
  (hper : ∀ k, ∀ b ∈ S k, ∀ p q, b.pt = some (p, q) →
    ∃ b' ∈ S (k + 1), b'.pt = some (p, q)) :
  ∀ j k, j ≤ k → ∀ b ∈ S j, ∀ p q, b.pt = some (p, q) →
    ∃ b' ∈ S k, b'.pt = some (p, q) := by
  intro j k
  induction k with
  | zero =>
    intro hjk b hb p q hpt
    have hj0 : j = 0 := by omega
    subst hj0
    exact ⟨b, hb, hpt⟩
  | succ k IH =>
    intro hjk b hb p q hpt
    obtain hlt | heq := lt_or_eq_of_le hjk
    · have hle : j ≤ k := by omega
      obtain ⟨b1, hb1, hpt1⟩ := IH hle b hb p q hpt
      exact hper k b1 hb1 p q hpt1
    · subst heq
      exact ⟨b, hb, hpt⟩

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[matchedX_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma matchedX_single {X Y : Type*} (b : Block X Y) :
  {x : X | ∃ t, b.pt = some (x, t)}.Finite := by
  by_cases hb : b.pt = none
  · have hempty : {x : X | ∃ t, b.pt = some (x, t)} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    obtain ⟨t, ht⟩ := h
    rw [hb] at ht
    exact Option.some_ne_none _ ht.symm
    rwa [hempty]
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists.mp hb
    obtain ⟨a, c⟩ := v
    have hsing : {x : X | ∃ t, b.pt = some (x, t)} = {a} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro h
        obtain ⟨t, ht⟩ := h
        rw [← hv] at ht
        have h2 : (a, c) = (x, t) := Option.some_inj.mp ht
        rwa [Prod.mk.injEq] at h2
      · intro h
        rw [h]
        exact ⟨c, by rw [hv]⟩
    rw [hsing]
    exact Set.finite_singleton a

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[matchedX_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma matchedX_finite {X Y : Type*} (s : Set (Block X Y))
  (hfin : s.Finite) :
  {x : X | ∃ t, ∃ b ∈ s, b.pt = some (x, t)}.Finite := by
  have hsub : {x : X | ∃ t, ∃ b ∈ s, b.pt = some (x, t)} =
    ⋃ b ∈ s, {x : X | ∃ t, b.pt = some (x, t)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨t, b, hb, hpt⟩ := h
      exact ⟨b, hb, t, hpt⟩
    · intro h
      obtain ⟨b, hb, t, hpt⟩ := h
      exact ⟨t, b, hb, hpt⟩
  rw [hsub]
  exact hfin.biUnion fun b _ => matchedX_single b

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[bound_preserveXS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma bound_preserveXS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] {s s' : Set (Block X Y)} {N : ℕ}
  (hgood : IsGoodS s)
  (hper : ∀ b ∈ s, ∀ p q, b.pt = some (p, q) → ∃ b' ∈ s', b'.pt = some (p, q))
  (hbnd : ∀ b' ∈ s', ∀ p q, b'.pt = some (p, q) → b' ∈ s ∨ b'.bound = N)
  {x : X} {y : Y} {b : Block X Y} (hb : b ∈ s)
  (hpt : b.pt = some (x, y)) (hbN : b.bound = N) :
  ∃ b' ∈ s', b'.pt = some (x, y) ∧ b'.bound = N := by
  obtain ⟨b', hb', hpt'⟩ := hper b hb x y hpt
  obtain hmem | hbound := hbnd b' hb' x y hpt'
  · have hx : x ∈ b.UX := (hgood.2.2.1 b hb x y hpt).1
    have hx' : x ∈ b'.UX := (hgood.2.2.1 b' hmem x y hpt').1
    have heq : b' = b := unique_block_XS hgood hmem hx' hb hx
    rw [heq] at hb' hpt'
    exact ⟨b, hb', hpt', hbN⟩
  · exact ⟨b', hb', hpt', hbound⟩

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[exists_shrinkXS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma exists_shrinkXS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] [T2Space X] [T2Space Y]
  [Countable X] [Countable Y] [PerfectSpace X] [PerfectSpace Y]
  {s : Set (Block X Y)} (hgood : IsGoodS s) (xstar : X) (N : ℕ) :
  ∃ s' : Set (Block X Y), IsGoodS s' ∧
    (∀ c' ∈ s', ∃ c ∈ s, c'.UX ⊆ c.UX ∧ c'.UY ⊆ c.UY) ∧
    (∀ b ∈ s, ∀ p q, b.pt = some (p, q) → ∃ b' ∈ s', b'.pt = some (p, q)) ∧
    (∃ t, ∃ b' ∈ s', b'.pt = some (xstar, t) ∧ b'.bound = N) ∧
    (∀ b' ∈ s', ∀ p q, b'.pt = some (p, q) → b' ∈ s ∨ b'.bound = N) := by
  by_cases hmatched : ∃ b ∈ s, ∃ t, b.pt = some (xstar, t)
  · obtain ⟨b0, hb0, t0, hpt0⟩ := hmatched
    have hcoverX := hgood.2.2.2.2.1.1
    obtain ⟨b, hb, hxb⟩ := hcoverX xstar
    have hx0 : xstar ∈ b0.UX := (hgood.2.2.1 b0 hb0 xstar t0 hpt0).1
    have ht0 : t0 ∈ b0.UY := (hgood.2.2.1 b0 hb0 xstar t0 hpt0).2
    have hbeq : b = b0 := unique_block_XS hgood hb hxb hb0 hx0
    have hbpt : b.pt = some (xstar, t0) := by
      rwa [hbeq]
    have hxb0 : xstar ∈ b.UX := hxb
    have ht0b : t0 ∈ b.UY := by
      rwa [hbeq]
    have hclopen := hgood.2.1 b hb
    obtain ⟨hbUX_clopen, hbUY_clopen, hbUX_ne, hbUY_ne⟩ := hclopen
    have hUX_inf : b.UX.Infinite :=
      infinite_of_nonempty_clopen hbUX_ne hbUX_clopen
    have hUY_inf : b.UY.Infinite :=
      infinite_of_nonempty_clopen hbUY_ne hbUY_clopen
    obtain ⟨z, hz_mem, hz_nmem⟩ :=
      hUX_inf.exists_notMem_finite (Set.finite_singleton xstar)
    have hz_ne : z ≠ xstar := fun heq =>
      hz_nmem (Set.mem_singleton_iff.mpr heq)
    obtain ⟨w, hw_mem, hw_nmem⟩ :=
      hUY_inf.exists_notMem_finite (Set.finite_singleton t0)
    have hw_ne : w ≠ t0 := fun heq =>
      hw_nmem (Set.mem_singleton_iff.mpr heq)
    have hε : (0 : ℝ) < 1 / ((N + 1 : ℕ) : ℝ) :=
      one_div_pos.mpr (Nat.cast_pos.mpr (by omega))
    have hxz : xstar ≠ z := Ne.symm hz_ne
    have htw : t0 ≠ w := Ne.symm hw_ne
    obtain ⟨Bx, Bz, hBx_cl, hBz_cl, hxBx, hzBz, hBxW, hBzW, hdisjX, hBx_ball,
      _⟩ := exists_disjoint_clopen hbUX_clopen hxb hz_mem hxz hε
    obtain ⟨By, Bw, hBy_cl, hBw_cl, htBy, hwBw, hByW, hBwW, hdisjY, hBy_ball,
      _⟩ := exists_disjoint_clopen hbUY_clopen ht0b hw_mem htw hε
    set LX : Set X := b.UX \ Bx with hLX
    set LY : Set Y := b.UY \ By with hLY
    have hBz_sub : Bz ⊆ LX := fun y hy =>
      (Set.mem_sdiff _).mpr ⟨hBzW hy, Set.disjoint_right.mp hdisjX hy⟩
    have hBw_sub : Bw ⊆ LY := fun y hy =>
      (Set.mem_sdiff _).mpr ⟨hBwW hy, Set.disjoint_right.mp hdisjY hy⟩
    have hLX_cl : IsClopen LX := hbUX_clopen.diff hBx_cl
    have hLY_cl : IsClopen LY := hbUY_clopen.diff hBy_cl
    have hLX_ne : LX.Nonempty := ⟨z, hBz_sub hzBz⟩
    have hLY_ne : LY.Nonempty := ⟨w, hBw_sub hwBw⟩
    set c1 : Block X Y := ⟨Bx, By, some (xstar, t0), N⟩ with hc1
    set c2 : Block X Y := ⟨LX, LY, none, 0⟩ with hc2
    set t : Set (Block X Y) := {c1, c2} with ht
    have hfin_t : t.Finite := by
      rw [ht]
      exact (Set.finite_singleton c2).insert c1
    have hclopen_t : ∀ c ∈ t,
      IsClopen c.UX ∧ IsClopen c.UY ∧ c.UX.Nonempty ∧ c.UY.Nonempty := by
      intro c hc
      rw [ht, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      obtain rfl | rfl := hc
      · rw [hc1]
        exact ⟨hBx_cl, hBy_cl, ⟨xstar, hxBx⟩, ⟨t0, htBy⟩⟩
      · rw [hc2]
        exact ⟨hLX_cl, hLY_cl, hLX_ne, hLY_ne⟩
    have hpts_t : ∀ c ∈ t, ∀ p q, c.pt = some (p, q) → p ∈ c.UX ∧ q ∈ c.UY := by
      intro c hc p q hpt
      rw [ht, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      obtain rfl | rfl := hc
      · rw [hc1] at hpt
        have hpair : (xstar, t0) = (p, q) := Option.some_inj.mp hpt
        rw [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        rw [hc1]
        exact ⟨hxBx, htBy⟩
      · rw [hc2] at hpt
        exact absurd hpt.symm (Option.some_ne_none _)
    have hdisj_t : ∀ c1' ∈ t, ∀ c2' ∈ t, c1' ≠ c2' →
      Disjoint c1'.UX c2'.UX ∧ Disjoint c1'.UY c2'.UY := by
      intro c1' hc1' c2' hc2' hne
      rw [ht, Set.mem_insert_iff, Set.mem_singleton_iff] at hc1' hc2'
      obtain rfl | rfl <;> rcases hc2' with rfl | rfl := hc1'
      · exact absurd rfl hne
      · rw [hc1, hc2]
        have hX : Disjoint Bx LX := by
          rw [hLX]
          exact Set.disjoint_left.mpr fun a ha1 ha2 =>
            (Set.mem_sdiff _).mp ha2 |>.2 ha1
        have hY : Disjoint By LY := by
          rw [hLY]
          exact Set.disjoint_left.mpr fun a ha1 ha2 =>
            (Set.mem_sdiff _).mp ha2 |>.2 ha1
        exact ⟨hX, hY⟩
      · rw [hc1, hc2]
        have hX : Disjoint LX Bx := by
          rw [hLX]
          exact Set.disjoint_left.mpr fun a ha1 ha2 =>
            (Set.mem_sdiff _).mp ha1 |>.2 ha2
        have hY : Disjoint LY By := by
          rw [hLY]
          exact Set.disjoint_left.mpr fun a ha1 ha2 =>
            (Set.mem_sdiff _).mp ha1 |>.2 ha2
        exact ⟨hX, hY⟩
      · exact absurd rfl hne
    have hsub_t : ∀ c ∈ t, c.UX ⊆ b.UX ∧ c.UY ⊆ b.UY := by
      intro c hc
      rw [ht, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      obtain rfl | rfl := hc
      · rw [hc1]
        exact ⟨hBxW, hByW⟩
      · rw [hc2, hLX, hLY]
        exact ⟨Set.sdiff_subset, Set.sdiff_subset⟩
    have hcoverX_t : ∀ x ∈ b.UX, ∃ c ∈ t, x ∈ c.UX := by
      intro x hx
      by_cases hxBx : x ∈ Bx
      · exact ⟨c1, Set.mem_insert c1 _, by rw [hc1]; exact hxBx⟩
      · have hxLX : x ∈ LX := (Set.mem_sdiff _).mpr ⟨hx, hxBx⟩
        have hc2t : c2 ∈ t := by
          rw [ht]
          exact Set.mem_insert_of_mem _
            (Set.mem_singleton_iff.mpr rfl)
        exact ⟨c2, hc2t, by rw [hc2]; exact hxLX⟩
    have hcoverY_t : ∀ y ∈ b.UY, ∃ c ∈ t, y ∈ c.UY := by
      intro y hy
      by_cases hyBy : y ∈ By
      · exact ⟨c1, Set.mem_insert c1 _, by rw [hc1]; exact hyBy⟩
      · have hyLY : y ∈ LY := (Set.mem_sdiff _).mpr ⟨hy, hyBy⟩
        have hc2t : c2 ∈ t := by
          rw [ht]
          exact Set.mem_insert_of_mem _
            (Set.mem_singleton_iff.mpr rfl)
        exact ⟨c2, hc2t, by rw [hc2]; exact hyLY⟩
    have hrad_t : ∀ c ∈ t, ∀ p q n, c.pt = some (p, q) → c.bound = n →
      c.UX ⊆ Metric.ball p (1 / ((n + 1 : ℕ) : ℝ)) ∧
      c.UY ⊆ Metric.ball q (1 / ((n + 1 : ℕ) : ℝ)) := by
      intro c hc p q n hpt hbound
      rw [ht, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      obtain rfl | rfl := hc
      · rw [hc1] at hpt hbound ⊢
        simp only at hbound
        subst hbound
        have hpair : (xstar, t0) = (p, q) := Option.some_inj.mp hpt
        rw [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        exact ⟨hBx_ball, hBy_ball⟩
      · rw [hc2] at hpt
        exact absurd hpt.symm (Option.some_ne_none _)
    obtain ⟨hgood', hrefine⟩ := isGood_replaceS hgood hb hfin_t hclopen_t
      hpts_t hdisj_t hsub_t hcoverX_t hcoverY_t hrad_t
    have hpersist : ∀ b0 ∈ s, ∀ p q, b0.pt = some (p, q) →
      ∃ b' ∈ t ∪ (s \ {b}), b'.pt = some (p, q) := by
      intro b0 hb0 p q hpt0
      by_cases heq : b0 = b
      · subst heq
        rw [hbpt] at hpt0
        have hpair : (xstar, t0) = (p, q) := Option.some_inj.mp hpt0
        rw [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        have hc1t : c1 ∈ t := by
          rw [ht]
          exact Set.mem_insert c1 _
        exact ⟨c1, Set.mem_union_left _ hc1t, by rw [hc1]⟩
      · have hmem : b0 ∈ s \ {b} := (Set.mem_sdiff _).mpr
        ⟨hb0, fun hmem => heq (Set.mem_singleton_iff.mp hmem)⟩
        exact ⟨b0, Set.mem_union_right _ hmem, hpt0⟩
    have hc1t : c1 ∈ t := by
      rw [ht]
      exact Set.mem_insert c1 _
    have hc1s' : c1 ∈ t ∪ (s \ {b}) := Set.mem_union_left _ hc1t
    have hpt1 : c1.pt = some (xstar, t0) := by rw [hc1]
    have hbnd1 : c1.bound = N := by rw [hc1]
    have hbnd_new : ∀ b' ∈ t ∪ (s \ {b}), ∀ p q, b'.pt = some (p, q) →
      b' ∈ s ∨ b'.bound = N := by
      intro b' hb' p q hpt
      rw [Set.mem_union] at hb'
      obtain hct | hcold := hb'
      · rw [ht, Set.mem_insert_iff, Set.mem_singleton_iff] at hct
        obtain rfl | rfl := hct
        · right
          rw [hc1]
        · rw [hc2] at hpt
          exact absurd hpt.symm (Option.some_ne_none _)
      · left
        exact (Set.mem_sdiff _).mp hcold |>.1
    exact ⟨t ∪ (s \ {b}), hgood', hrefine, hpersist, ⟨t0, c1, hc1s', hpt1, hbnd1⟩,
      hbnd_new⟩
  · obtain ⟨s', hgood', href', hper', hmatch', hbnd'⟩ :=
    exists_forwardS hgood xstar N
    obtain ⟨t, b', hb', hpt'⟩ := hmatch'
    have hbN : b'.bound = N := by
      obtain hmem | hN := hbnd' b' hb' xstar t hpt'
      · exfalso
        exact hmatched ⟨b', hmem, t, hpt'⟩
      · exact hN
    exact ⟨s', hgood', href', hper', ⟨t, b', hb', hpt', hbN⟩, hbnd'⟩

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[exists_shrinkYS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma exists_shrinkYS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] [T2Space X] [T2Space Y]
  [Countable X] [Countable Y] [PerfectSpace X] [PerfectSpace Y]
  {s : Set (Block X Y)} (hgood : IsGoodS s) (ystar : Y) (N : ℕ) :
  ∃ s' : Set (Block X Y), IsGoodS s' ∧
    (∀ c' ∈ s', ∃ c ∈ s, c'.UX ⊆ c.UX ∧ c'.UY ⊆ c.UY) ∧
    (∀ b ∈ s, ∀ p q, b.pt = some (p, q) → ∃ b' ∈ s', b'.pt = some (p, q)) ∧
    (∃ s_, ∃ b' ∈ s', b'.pt = some (s_, ystar) ∧ b'.bound = N) ∧
    (∀ b' ∈ s', ∀ p q, b'.pt = some (p, q) → b' ∈ s ∨ b'.bound = N) := by
  have hgoodSwap : IsGoodS (Block.swap '' s) := isGoodS_swap hgood
  obtain ⟨t', hgood', href', hper', hmatch', hbnd'⟩ :=
    exists_shrinkXS hgoodSwap ystar N
  obtain ⟨s_, d', hd', hpt', hbN'⟩ := hmatch'
  refine ⟨Block.swap '' t', isGoodS_swap hgood', ?_, ?_, ?_, ?_⟩
  · intro c' hc'
    obtain ⟨d, hd, rfl⟩ := (Set.mem_image _ _ _).mp hc'
    obtain ⟨d0, hd0, hX0, hY0⟩ := href' d hd
    obtain ⟨c, hc, rfl⟩ := (Set.mem_image _ _ _).mp hd0
    exact ⟨c, hc, hY0, hX0⟩
  · intro b hb p q hpt
    have hbSwap : Block.swap b ∈ Block.swap '' s := Set.mem_image_of_mem _ hb
    have hptSwap : (Block.swap b).pt = some (q, p) := (Block.swap_pt b q p).mpr hpt
    obtain ⟨d', hd', hptd'⟩ := hper' (Block.swap b) hbSwap q p hptSwap
    exact ⟨Block.swap d', Set.mem_image_of_mem _ hd',
      (Block.swap_pt d' p q).mpr hptd'⟩
  · exact ⟨s_, Block.swap d', Set.mem_image_of_mem _ hd',
    (Block.swap_pt d' s_ ystar).mpr hpt', hbN'⟩
  · intro b' hb' p q hpt
    obtain ⟨d, hd, rfl⟩ := (Set.mem_image _ _ _).mp hb'
    have hptd : d.pt = some (q, p) := (Block.swap_pt d p q).mp hpt
    obtain h | h := hbnd' d hd q p hptd
    · obtain ⟨c, hc, rfl⟩ := (Set.mem_image _ _ _).mp h
      left
      rwa [Block.swap_swap]
    · right
      exact h

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[exists_shrink_listXS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma exists_shrink_listXS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] [T2Space X] [T2Space Y]
  [Countable X] [Countable Y] [PerfectSpace X] [PerfectSpace Y]
  {s : Set (Block X Y)} (hgood : IsGoodS s) (L : List X) (N : ℕ) :
  ∃ s' : Set (Block X Y), IsGoodS s' ∧
    (∀ c' ∈ s', ∃ c ∈ s, c'.UX ⊆ c.UX ∧ c'.UY ⊆ c.UY) ∧
    (∀ b ∈ s, ∀ p q, b.pt = some (p, q) → ∃ b' ∈ s', b'.pt = some (p, q)) ∧
    (∀ x ∈ L, ∃ y, ∃ b' ∈ s', b'.pt = some (x, y) ∧ b'.bound = N) ∧
    (∀ b' ∈ s', ∀ p q, b'.pt = some (p, q) → b' ∈ s ∨ b'.bound = N) := by
  induction L generalizing s with
  | nil =>
    refine ⟨s, hgood, ?_, ?_, ?_, ?_⟩
    · intro c' hc'
      exact ⟨c', hc', Subset.rfl, Subset.rfl⟩
    · intro b hb p q hpt
      exact ⟨b, hb, hpt⟩
    · intro x hx
      simp only [List.mem_nil_iff] at hx
    · intro b' hb' _ _ _
      exact Or.inl hb'
  | cons x xs IH =>
    obtain ⟨s1, hgood1, href1, hper1, hmatch1, hbnd1⟩ := IH hgood
    obtain ⟨s2, hgood2, href2, hper2, hmatch2, hbnd2⟩ :=
      exists_shrinkXS hgood1 x N
    obtain ⟨y0, b0, hb0, hpt0, hbN0⟩ := hmatch2
    refine ⟨s2, hgood2, ?_, ?_, ?_, ?_⟩
    · intro c' hc'
      obtain ⟨c1, hc1, hX1, hY1⟩ := href2 c' hc'
      obtain ⟨c, hc, hX, hY⟩ := href1 c1 hc1
      exact ⟨c, hc, hX1.trans hX, hY1.trans hY⟩
    · intro b hb p q hpt
      obtain ⟨b1, hb1, hpt1⟩ := hper1 b hb p q hpt
      exact hper2 b1 hb1 p q hpt1
    · intro y hy
      rw [List.mem_cons] at hy
      obtain rfl | hmem := hy
      · exact ⟨y0, b0, hb0, hpt0, hbN0⟩
      · obtain ⟨t, b1, hb1, hpt1, hbN1⟩ := hmatch1 y hmem
        exact ⟨t, bound_preserveXS hgood1 hper2 hbnd2 hb1 hpt1 hbN1⟩
    · intro b' hb' p q hpt
      obtain h | h := hbnd2 b' hb' p q hpt
      · rcases hbnd1 b' h p q hpt with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
      · exact Or.inr h

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[exists_shrink_listYS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma exists_shrink_listYS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] [T2Space X] [T2Space Y]
  [Countable X] [Countable Y] [PerfectSpace X] [PerfectSpace Y]
  {s : Set (Block X Y)} (hgood : IsGoodS s) (L : List Y) (N : ℕ) :
  ∃ s' : Set (Block X Y), IsGoodS s' ∧
    (∀ c' ∈ s', ∃ c ∈ s, c'.UX ⊆ c.UX ∧ c'.UY ⊆ c.UY) ∧
    (∀ b ∈ s, ∀ p q, b.pt = some (p, q) → ∃ b' ∈ s', b'.pt = some (p, q)) ∧
    (∀ y ∈ L, ∃ x, ∃ b' ∈ s', b'.pt = some (x, y) ∧ b'.bound = N) ∧
    (∀ b' ∈ s', ∀ p q, b'.pt = some (p, q) → b' ∈ s ∨ b'.bound = N) := by
  induction L generalizing s with
  | nil =>
    refine ⟨s, hgood, ?_, ?_, ?_, ?_⟩
    · intro c' hc'
      exact ⟨c', hc', Subset.rfl, Subset.rfl⟩
    · intro b hb p q hpt
      exact ⟨b, hb, hpt⟩
    · intro y hy
      simp only [List.mem_nil_iff] at hy
    · intro b' hb' _ _ _
      exact Or.inl hb'
  | cons y ys IH =>
    obtain ⟨s1, hgood1, href1, hper1, hmatch1, hbnd1⟩ := IH hgood
    obtain ⟨s2, hgood2, href2, hper2, hmatch2, hbnd2⟩ :=
      exists_shrinkYS hgood1 y N
    obtain ⟨x0, b0, hb0, hpt0, hbN0⟩ := hmatch2
    refine ⟨s2, hgood2, ?_, ?_, ?_, ?_⟩
    · intro c' hc'
      obtain ⟨c1, hc1, hX1, hY1⟩ := href2 c' hc'
      obtain ⟨c, hc, hX, hY⟩ := href1 c1 hc1
      exact ⟨c, hc, hX1.trans hX, hY1.trans hY⟩
    · intro b hb p q hpt
      obtain ⟨b1, hb1, hpt1⟩ := hper1 b hb p q hpt
      exact hper2 b1 hb1 p q hpt1
    · intro z hz
      rw [List.mem_cons] at hz
      obtain rfl | hmem := hz
      · exact ⟨x0, b0, hb0, hpt0, hbN0⟩
      · obtain ⟨s_, b1, hb1, hpt1, hbN1⟩ := hmatch1 z hmem
        obtain ⟨b2, hb2, hpt2, hbN2⟩ :=
          bound_preserveXS hgood1 hper2 hbnd2 hb1 hpt1 hbN1
        exact ⟨s_, b2, hb2, hpt2, hbN2⟩
    · intro b' hb' p q hpt
      obtain h | h := hbnd2 b' hb' p q hpt
      · rcases hbnd1 b' h p q hpt with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
      · exact Or.inr h

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[exists_stageXS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma exists_stageXS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] [T2Space X] [T2Space Y]
  [Countable X] [Countable Y] [PerfectSpace X] [PerfectSpace Y]
  (eX : ℕ → X) (eY : ℕ → Y)
  {s : Set (Block X Y)} (hgood : IsGoodS s) (N : ℕ) :
  ∃ s' : Set (Block X Y), IsGoodS s' ∧
    (∀ c' ∈ s', ∃ c ∈ s, c'.UX ⊆ c.UX ∧ c'.UY ⊆ c.UY) ∧
    (∀ b ∈ s, ∀ p q, b.pt = some (p, q) → ∃ b' ∈ s', b'.pt = some (p, q)) ∧
    (∀ i ≤ N, ∃ y, ∃ b' ∈ s', b'.pt = some (eX i, y) ∧ b'.bound = N) ∧
    (∀ j ≤ N, ∃ x, ∃ b' ∈ s', b'.pt = some (x, eY j) ∧ b'.bound = N) ∧
    (∀ b' ∈ s', ∀ p q, b'.pt = some (p, q) → b' ∈ s ∨ b'.bound = N) := by
  have hLXmem : ∀ i ≤ N, eX i ∈ (List.range (N + 1)).map eX := by
    intro i hi
    rw [List.mem_map]
    exact ⟨i, List.mem_range.mpr (by omega), rfl⟩
  have hLYmem : ∀ j ≤ N, eY j ∈ (List.range (N + 1)).map eY := by
    intro j hj
    rw [List.mem_map]
    exact ⟨j, List.mem_range.mpr (by omega), rfl⟩
  obtain ⟨s1, hgood1, href1, hper1, hmatch1, hbnd1⟩ :=
    exists_shrink_listXS hgood ((List.range (N + 1)).map eX) N
  obtain ⟨s2, hgood2, href2, hper2, hmatch2, hbnd2⟩ :=
    exists_shrink_listYS hgood1 ((List.range (N + 1)).map eY) N
  refine ⟨s2, hgood2, ?_, ?_, ?_, ?_, ?_⟩
  · intro c' hc'
    obtain ⟨c1, hc1, hX1, hY1⟩ := href2 c' hc'
    obtain ⟨c, hc, hX, hY⟩ := href1 c1 hc1
    exact ⟨c, hc, hX1.trans hX, hY1.trans hY⟩
  · intro b hb p q hpt
    obtain ⟨b1, hb1, hpt1⟩ := hper1 b hb p q hpt
    exact hper2 b1 hb1 p q hpt1
  · intro i hi
    obtain ⟨t, b1, hb1, hpt1, hbN1⟩ := hmatch1 (eX i) (hLXmem i hi)
    exact ⟨t, bound_preserveXS hgood1 hper2 hbnd2 hb1 hpt1 hbN1⟩
  · intro j hj
    exact hmatch2 (eY j) (hLYmem j hj)
  · intro b' hb' p q hpt
    obtain h | h := hbnd2 b' hb' p q hpt
    · rcases hbnd1 b' h p q hpt with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · exact Or.inr h

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[exists_backforth_sequence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma exists_backforth_sequence {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] [T2Space X] [T2Space Y]
  [Countable X] [Countable Y] [PerfectSpace X] [PerfectSpace Y]
  [Nonempty X] [Nonempty Y] (eX : ℕ → X) (eY : ℕ → Y) :
  ∃ S : ℕ → Set (Block X Y),
    S 0 = ({⟨Set.univ, Set.univ, none, 0⟩} : Set (Block X Y)) ∧
    (∀ n, IsGoodS (S n)) ∧
    (∀ n, ∀ c' ∈ S (n + 1), ∃ c ∈ S n, c'.UX ⊆ c.UX ∧ c'.UY ⊆ c.UY) ∧
    (∀ n, ∀ b ∈ S n, ∀ p q, b.pt = some (p, q) →
      ∃ b' ∈ S (n + 1), b'.pt = some (p, q)) ∧
    (∀ n, ∀ i ≤ n, ∃ y, ∃ b' ∈ S (n + 1),
      b'.pt = some (eX i, y) ∧ b'.bound = n) ∧
    (∀ n, ∀ j ≤ n, ∃ x, ∃ b' ∈ S (n + 1),
      b'.pt = some (x, eY j) ∧ b'.bound = n) := by
  have hstep : ∀ s : Set (Block X Y), ∀ N : ℕ, ∃ s' : Set (Block X Y),
    (IsGoodS s → IsGoodS s' ∧
      (∀ c' ∈ s', ∃ c ∈ s, c'.UX ⊆ c.UX ∧ c'.UY ⊆ c.UY) ∧
      (∀ b ∈ s, ∀ p q, b.pt = some (p, q) → ∃ b' ∈ s', b'.pt = some (p, q)) ∧
      (∀ i ≤ N, ∃ y, ∃ b' ∈ s', b'.pt = some (eX i, y) ∧ b'.bound = N) ∧
      (∀ j ≤ N, ∃ x, ∃ b' ∈ s', b'.pt = some (x, eY j) ∧ b'.bound = N)) := by
    intro s N
    by_cases hgood : IsGoodS s
    · obtain ⟨s', hgood', href', hper', hmatchX', hmatchY', _⟩ :=
      exists_stageXS eX eY hgood N
      exact ⟨s', fun _ => ⟨hgood', href', hper', hmatchX', hmatchY'⟩⟩
    · exact ⟨s, fun h => absurd h hgood⟩
  choose next hnext using hstep
  let S : ℕ → Set (Block X Y) :=
    Nat.rec ({⟨Set.univ, Set.univ, none, 0⟩} : Set (Block X Y))
      (fun n IH => next IH n)
  have hS0 : S 0 = ({⟨Set.univ, Set.univ, none, 0⟩} : Set (Block X Y)) := rfl
  have hSsucc : ∀ n, S (n + 1) = next (S n) n := fun n => rfl
  have hgoodS : ∀ n, IsGoodS (S n) := by
    intro n
    induction n with
    | zero =>
      rwa [hS0]
    | succ n IH =>
      rw [hSsucc n]
      exact ((hnext (S n) n) IH).1
  refine ⟨S, hS0, hgoodS, ?_, ?_, ?_, ?_⟩
  · intro n c' hc'
    rw [hSsucc n] at hc'
    obtain ⟨_, href, _, _, _⟩ := (hnext (S n) n) (hgoodS n)
    exact href c' hc'
  · intro n b hb p q hpt
    rw [hSsucc n]
    obtain ⟨_, _, hper, _, _⟩ := (hnext (S n) n) (hgoodS n)
    exact hper b hb p q hpt
  · intro n i hi
    rw [hSsucc n]
    obtain ⟨_, _, _, hmatchX, _⟩ := (hnext (S n) n) (hgoodS n)
    exact hmatchX i hi
  · intro n j hj
    rw [hSsucc n]
    obtain ⟨_, _, _, _, hmatchY⟩ := (hnext (S n) n) (hgoodS n)
    exact hmatchY j hj

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[match_unique_acrossXS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma match_unique_acrossXS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y]
  {S : ℕ → Set (Block X Y)} (hgoodS : ∀ n, IsGoodS (S n))
  (hperS : ∀ n, ∀ b ∈ S n, ∀ p q, b.pt = some (p, q) →
    ∃ b' ∈ S (n + 1), b'.pt = some (p, q))
  {x : X} {t1 t2 : Y} {n1 n2 : ℕ} {b1 b2 : Block X Y}
  (h1 : b1 ∈ S n1) (hpt1 : b1.pt = some (x, t1))
  (h2 : b2 ∈ S n2) (hpt2 : b2.pt = some (x, t2)) : t1 = t2 := by
  have hle1 : n1 ≤ Nat.max n1 n2 := Nat.le_max_left n1 n2
  have hle2 : n2 ≤ Nat.max n1 n2 := Nat.le_max_right n1 n2
  obtain ⟨b1', hb1', hpt1'⟩ :=
    persist_le_of_step S hperS n1 (Nat.max n1 n2) hle1 b1 h1 x t1 hpt1
  obtain ⟨b2', hb2', hpt2'⟩ :=
    persist_le_of_step S hperS n2 (Nat.max n1 n2) hle2 b2 h2 x t2 hpt2
  exact matched_unique_XS (hgoodS (Nat.max n1 n2)) hb1' hpt1' hb2' hpt2'

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[match_unique_acrossYS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma match_unique_acrossYS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y]
  {S : ℕ → Set (Block X Y)} (hgoodS : ∀ n, IsGoodS (S n))
  (hperS : ∀ n, ∀ b ∈ S n, ∀ p q, b.pt = some (p, q) →
    ∃ b' ∈ S (n + 1), b'.pt = some (p, q))
  {y : Y} {s1 s2 : X} {n1 n2 : ℕ} {b1 b2 : Block X Y}
  (h1 : b1 ∈ S n1) (hpt1 : b1.pt = some (s1, y))
  (h2 : b2 ∈ S n2) (hpt2 : b2.pt = some (s2, y)) : s1 = s2 := by
  have hle1 : n1 ≤ Nat.max n1 n2 := Nat.le_max_left n1 n2
  have hle2 : n2 ≤ Nat.max n1 n2 := Nat.le_max_right n1 n2
  obtain ⟨b1', hb1', hpt1'⟩ :=
    persist_le_of_step S hperS n1 (Nat.max n1 n2) hle1 b1 h1 s1 y hpt1
  obtain ⟨b2', hb2', hpt2'⟩ :=
    persist_le_of_step S hperS n2 (Nat.max n1 n2) hle2 b2 h2 s2 y hpt2
  exact matched_unique_YS (hgoodS (Nat.max n1 n2)) hb1' hpt1' hb2' hpt2'

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[match_memXS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma match_memXS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y]
  {S : ℕ → Set (Block X Y)} (hgoodS : ∀ n, IsGoodS (S n))
  (hrefS : ∀ n, ∀ c' ∈ S (n + 1), ∃ c ∈ S n, c'.UX ⊆ c.UX ∧ c'.UY ⊆ c.UY)
  (hperS : ∀ n, ∀ b ∈ S n, ∀ p q, b.pt = some (p, q) →
    ∃ b' ∈ S (n + 1), b'.pt = some (p, q))
  {k j : ℕ} {b b0 : Block X Y} (hb : b ∈ S k) {x' : X} (hx' : x' ∈ b.UX)
  (hb0 : b0 ∈ S j) {y' : Y} (hpt0 : b0.pt = some (x', y')) : y' ∈ b.UY := by
  have hleKk : k ≤ Nat.max k j := Nat.le_max_left k j
  have hleKj : j ≤ Nat.max k j := Nat.le_max_right k j
  obtain ⟨b1, hb1, hpt1⟩ :=
    persist_le_of_step S hperS j (Nat.max k j) hleKj b0 hb0 x' y' hpt0
  obtain ⟨c, hc, hX, hY⟩ :=
    refine_le_of_step S hrefS k (Nat.max k j) hleKk b1 hb1
  have hx1 : x' ∈ b1.UX := (hgoodS (Nat.max k j)).2.2.1 b1 hb1 x' y' hpt1 |>.1
  have hxc : x' ∈ c.UX := hX hx1
  have hceq : c = b := unique_block_XS (hgoodS k) hc hxc hb hx'
  have hy1 : y' ∈ b1.UY := (hgoodS (Nat.max k j)).2.2.1 b1 hb1 x' y' hpt1 |>.2
  have hy : y' ∈ c.UY := hY hy1
  rwa [hceq] at hy

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[match_memYS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma match_memYS {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y]
  {S : ℕ → Set (Block X Y)} (hgoodS : ∀ n, IsGoodS (S n))
  (hrefS : ∀ n, ∀ c' ∈ S (n + 1), ∃ c ∈ S n, c'.UX ⊆ c.UX ∧ c'.UY ⊆ c.UY)
  (hperS : ∀ n, ∀ b ∈ S n, ∀ p q, b.pt = some (p, q) →
    ∃ b' ∈ S (n + 1), b'.pt = some (p, q))
  {k j : ℕ} {b b0 : Block X Y} (hb : b ∈ S k) {y' : Y} (hy' : y' ∈ b.UY)
  (hb0 : b0 ∈ S j) {x' : X} (hpt0 : b0.pt = some (x', y')) : x' ∈ b.UX := by
  have hleKk : k ≤ Nat.max k j := Nat.le_max_left k j
  have hleKj : j ≤ Nat.max k j := Nat.le_max_right k j
  obtain ⟨b1, hb1, hpt1⟩ :=
    persist_le_of_step S hperS j (Nat.max k j) hleKj b0 hb0 x' y' hpt0
  obtain ⟨c, hc, hX, hY⟩ :=
    refine_le_of_step S hrefS k (Nat.max k j) hleKk b1 hb1
  have hy1 : y' ∈ b1.UY := (hgoodS (Nat.max k j)).2.2.1 b1 hb1 x' y' hpt1 |>.2
  have hyc : y' ∈ c.UY := hY hy1
  have hceq : c = b := unique_block_YS (hgoodS k) hc hyc hb hy'
  have hx1 : x' ∈ b1.UX := (hgoodS (Nat.max k j)).2.2.1 b1 hb1 x' y' hpt1 |>.1
  have hx : x' ∈ c.UX := hX hx1
  rwa [hceq] at hx

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/--
[sierpinski_rationals_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
lemma sierpinski_rationals_characterization
  [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [PerfectSpace X] [Countable X] [Nonempty X] :
-- imply
  Nonempty (X ≃ₜ ℚ) := by
-- proof
  let : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  have : PerfectSpace ℚ := perfectSpace_rat
  obtain ⟨eX, heX⟩ := exists_surjective_nat X
  obtain ⟨eY, heY⟩ := exists_surjective_nat ℚ
  obtain ⟨S, hS0, hgoodS, hrefS, hperS, hmatchXS, hmatchYS⟩ :=
    exists_backforth_sequence (X := X) (Y := ℚ) eX eY
  have hXex : ∀ x : X, ∃ y : ℚ, ∃ n, ∃ b ∈ S n, b.pt = some (x, y) := by
    intro x
    obtain ⟨m, hm⟩ := heX x
    obtain ⟨y, b', hb', hpt', _⟩ := hmatchXS m m le_rfl
    rw [hm] at hpt'
    exact ⟨y, m + 1, b', hb', hpt'⟩
  have hYex : ∀ y : ℚ, ∃ x : X, ∃ n, ∃ b ∈ S n, b.pt = some (x, y) := by
    intro y
    obtain ⟨m, hm⟩ := heY y
    obtain ⟨x, b', hb', hpt', _⟩ := hmatchYS m m le_rfl
    rw [hm] at hpt'
    exact ⟨x, m + 1, b', hb', hpt'⟩
  have hXuniq : ∀ x y1 y2, (∃ n1, ∃ b1 ∈ S n1, b1.pt = some (x, y1)) →
    (∃ n2, ∃ b2 ∈ S n2, b2.pt = some (x, y2)) → y1 = y2 := by
    intro x y1 y2 h1 h2
    obtain ⟨n1, b1, hb1, hpt1⟩ := h1
    obtain ⟨n2, b2, hb2, hpt2⟩ := h2
    exact match_unique_acrossXS hgoodS hperS hb1 hpt1 hb2 hpt2
  have hYuniq : ∀ y x1 x2, (∃ n1, ∃ b1 ∈ S n1, b1.pt = some (x1, y)) →
    (∃ n2, ∃ b2 ∈ S n2, b2.pt = some (x2, y)) → x1 = x2 := by
    intro y x1 x2 h1 h2
    obtain ⟨n1, b1, hb1, hpt1⟩ := h1
    obtain ⟨n2, b2, hb2, hpt2⟩ := h2
    exact match_unique_acrossYS hgoodS hperS hb1 hpt1 hb2 hpt2
  choose f hf using hXex
  choose g hg using hYex
  have hgf : ∀ x, g (f x) = x := by
    intro x
    obtain ⟨n1, b1, hb1, hpt1⟩ := hf x
    obtain ⟨n2, b2, hb2, hpt2⟩ := hg (f x)
    exact (match_unique_acrossYS hgoodS hperS hb1 hpt1 hb2 hpt2).symm
  have hfg : ∀ y, f (g y) = y := by
    intro y
    obtain ⟨n1, b1, hb1, hpt1⟩ := hg y
    obtain ⟨n2, b2, hb2, hpt2⟩ := hf (g y)
    exact (match_unique_acrossXS hgoodS hperS hb1 hpt1 hb2 hpt2).symm
  have hcont_f : Continuous f := by
    rw [Metric.continuous_iff]
    intro x ε hε
    obtain ⟨m, hm⟩ := heX x
    have harch : ∃ N0 : ℕ, 1 / ((N0 + 1 : ℕ) : ℝ) < ε := by
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      refine ⟨N, ?_⟩
      have hNpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
        have h : (0 : ℕ) < N + 1 := by omega
        exact_mod_cast h
      have h1ε_lt : (1 : ℝ) / ε < ((N + 1 : ℕ) : ℝ) := by
        have hNN1 : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
          have hle : N ≤ N + 1 := by omega
          exact_mod_cast hle
        exact lt_of_lt_of_le hN hNN1
      have h1εpos : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε
      have h := one_div_lt_one_div_of_lt h1εpos h1ε_lt
      have hone : (1 : ℝ) / (1 / ε) = ε := by
        rw [one_div, one_div, inv_inv]
      rwa [hone] at h
    obtain ⟨N0, hN0⟩ := harch
    let N : ℕ := Nat.max m N0
    have hmN : m ≤ N := Nat.le_max_left m N0
    have hN0N : N0 ≤ N := Nat.le_max_right m N0
    have hNε : 1 / ((N + 1 : ℕ) : ℝ) < ε := by
      have hpos1 : (0 : ℝ) < ((N0 + 1 : ℕ) : ℝ) := by
        have h : (0 : ℕ) < N0 + 1 := by omega
        exact_mod_cast h
      have hle : ((N0 + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        have hleN : N0 + 1 ≤ N + 1 := by omega
        exact_mod_cast hleN
      have hle_div : 1 / ((N + 1 : ℕ) : ℝ) ≤ 1 / ((N0 + 1 : ℕ) : ℝ) :=
        one_div_le_one_div_of_le hpos1 hle
      exact lt_of_le_of_lt hle_div hN0
    obtain ⟨y0, b, hb, hpt, hbN⟩ := hmatchXS N m hmN
    rw [hm] at hpt
    have hy0 : y0 = f x :=
      hXuniq x y0 (f x) ⟨N + 1, b, hb, hpt⟩ (hf x)
    subst hy0
    have hbound := (hgoodS (N + 1)).2.2.2.2.2 b hb x (f x) N hpt hbN
    obtain ⟨hXball, hYball⟩ := hbound
    have hopen : IsOpen b.UX := ((hgoodS (N + 1)).2.1 b hb).1.isOpen
    have hxU : x ∈ b.UX := ((hgoodS (N + 1)).2.2.1 b hb x (f x) hpt).1
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hxU)
    refine ⟨δ, hδpos, ?_⟩
    intro x' hx'
    have hx'U : x' ∈ b.UX := hδsub (Metric.mem_ball.mpr hx')
    obtain ⟨j, b0, hb0, hpt0⟩ := hf x'
    have hy' : f x' ∈ b.UY := match_memXS hgoodS hrefS hperS hb hx'U hb0 hpt0
    have hmem : f x' ∈ Metric.ball (f x) (1 / ((N + 1 : ℕ) : ℝ)) := hYball hy'
    have hdist : dist (f x') (f x) < 1 / ((N + 1 : ℕ) : ℝ) :=
      Metric.mem_ball.mp hmem
    exact lt_trans hdist hNε
  have hcont_g : Continuous g := by
    rw [Metric.continuous_iff]
    intro y ε hε
    obtain ⟨m, hm⟩ := heY y
    have harch : ∃ N0 : ℕ, 1 / ((N0 + 1 : ℕ) : ℝ) < ε := by
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      refine ⟨N, ?_⟩
      have hNpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
        have h : (0 : ℕ) < N + 1 := by omega
        exact_mod_cast h
      have h1ε_lt : (1 : ℝ) / ε < ((N + 1 : ℕ) : ℝ) := by
        have hNN1 : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
          have hle : N ≤ N + 1 := by omega
          exact_mod_cast hle
        exact lt_of_lt_of_le hN hNN1
      have h1εpos : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε
      have h := one_div_lt_one_div_of_lt h1εpos h1ε_lt
      have hone : (1 : ℝ) / (1 / ε) = ε := by
        rw [one_div, one_div, inv_inv]
      rwa [hone] at h
    obtain ⟨N0, hN0⟩ := harch
    let N : ℕ := Nat.max m N0
    have hmN : m ≤ N := Nat.le_max_left m N0
    have hN0N : N0 ≤ N := Nat.le_max_right m N0
    have hNε : 1 / ((N + 1 : ℕ) : ℝ) < ε := by
      have hpos1 : (0 : ℝ) < ((N0 + 1 : ℕ) : ℝ) := by
        have h : (0 : ℕ) < N0 + 1 := by omega
        exact_mod_cast h
      have hle : ((N0 + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        have hleN : N0 + 1 ≤ N + 1 := by omega
        exact_mod_cast hleN
      have hle_div : 1 / ((N + 1 : ℕ) : ℝ) ≤ 1 / ((N0 + 1 : ℕ) : ℝ) :=
        one_div_le_one_div_of_le hpos1 hle
      exact lt_of_le_of_lt hle_div hN0
    obtain ⟨x0, b, hb, hpt, hbN⟩ := hmatchYS N m hmN
    rw [hm] at hpt
    have hx0 : x0 = g y :=
      hYuniq y x0 (g y) ⟨N + 1, b, hb, hpt⟩ (hg y)
    subst hx0
    have hbound := (hgoodS (N + 1)).2.2.2.2.2 b hb (g y) y N hpt hbN
    obtain ⟨hXball, hYball⟩ := hbound
    have hopen : IsOpen b.UY := ((hgoodS (N + 1)).2.1 b hb).2.1.isOpen
    have hyU : y ∈ b.UY := ((hgoodS (N + 1)).2.2.1 b hb (g y) y hpt).2
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hyU)
    refine ⟨δ, hδpos, ?_⟩
    intro y' hy'
    have hy'U : y' ∈ b.UY := hδsub (Metric.mem_ball.mpr hy')
    obtain ⟨j, b0, hb0, hpt0⟩ := hg y'
    have hx' : g y' ∈ b.UX := match_memYS hgoodS hrefS hperS hb hy'U hb0 hpt0
    have hmem : g y' ∈ Metric.ball (g y) (1 / ((N + 1 : ℕ) : ℝ)) := hXball hx'
    have hdist : dist (g y') (g y) < 1 / ((N + 1 : ℕ) : ℝ) :=
      Metric.mem_ball.mp hmem
    exact lt_trans hdist hNε
  let e : X ≃ ℚ := ⟨f, g, hgf, hfg⟩
  exact ⟨⟨e, hcont_f, hcont_g⟩⟩
end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted



-- created on 2026-10-20
-- updated on 2026-10-23
