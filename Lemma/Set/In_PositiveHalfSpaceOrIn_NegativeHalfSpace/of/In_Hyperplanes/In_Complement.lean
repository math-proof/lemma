import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Reflection.WallSeparation
open Set HyperplaneArrangement
open scoped InnerProductSpace


namespace HyperplaneArrangement

/--
[complement_mem_halfSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma complement_mem_halfSpace
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {x : E}
  {η : AffineHyperplane E}
-- given
  (hx : x ∈ arr.complement)
  (hη : η ∈ arr.hyperplanes) :
-- imply
  x ∈ η.positiveHalfSpace ∨ x ∈ η.negativeHalfSpace := by
-- proof
  simp only [HyperplaneArrangement.complement, Set.mem_diff, Set.mem_univ, true_and,
    HyperplaneArrangement.unionSet] at hx
  have hx' : x ∉ η.carrier := by
    intro habs
    exact hx (Set.mem_biUnion hη habs)
  simp only [AffineHyperplane.carrier, AffineHyperplane.positiveHalfSpace,
    AffineHyperplane.negativeHalfSpace, Set.mem_setOf_eq] at hx' ⊢
  exact lt_or_gt_of_ne (Ne.symm hx')

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[positiveHalfSpace_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma positiveHalfSpace_isOpen
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {η : AffineHyperplane E} :
-- imply
  IsOpen η.positiveHalfSpace :=
-- proof
  HalfSpaceOpen η

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[negativeHalfSpace_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma negativeHalfSpace_isOpen
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {η : AffineHyperplane E} :
-- imply
  IsOpen η.negativeHalfSpace := by
-- proof
  apply isOpen_lt
  exact continuous_const.inner continuous_id
  exact continuous_const

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[halfSpaces_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma halfSpaces_disjoint
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {η : AffineHyperplane E} :
-- imply
  Disjoint η.positiveHalfSpace η.negativeHalfSpace := by
-- proof
  rw [Set.disjoint_iff]
  intro z ⟨hz1, hz2⟩
  simp only [AffineHyperplane.positiveHalfSpace, AffineHyperplane.negativeHalfSpace,
    Set.mem_setOf_eq] at hz1 hz2
  linarith

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[negativeHalfSpace_convex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma negativeHalfSpace_convex
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {η : AffineHyperplane E} :
-- imply
  Convex ℝ η.negativeHalfSpace := by
-- proof
  intro x hx y hy a b ha hb hab
  simp only [AffineHyperplane.negativeHalfSpace, Set.mem_setOf_eq] at *
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  obtain rfl | ha_pos := eq_or_lt_of_le ha
  · simp at hab; subst hab; simp; linarith
  · rcases eq_or_lt_of_le hb with rfl | hb_pos
    · simp at hab; subst hab; simp; linarith
    · have h1 := mul_lt_mul_of_pos_left hx ha_pos
      have h2 := mul_lt_mul_of_pos_left hy hb_pos
      have h3 : a * η.offset + b * η.offset = η.offset := by
        have := congr_arg (· * η.offset) hab; simp [add_mul] at this; linarith
      linarith

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[connected_subset_in_positive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma connected_subset_in_positive
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {S : Set E}
  {η : AffineHyperplane E}
  {x : E}
-- given
  (hS : IsPreconnected S)
  (hcomp : S ⊆ arr.complement)
  (hη : η ∈ arr.hyperplanes)
  (hx : x ∈ S)
  (hxp : x ∈ η.positiveHalfSpace) :
-- imply
  S ⊆ η.positiveHalfSpace := by
-- proof
  intro y hy
  by_contra hyp
  have hy_comp := hcomp hy
  obtain h | h := complement_mem_halfSpace hy_comp hη
  · exact hyp h
  · have hS_sub : S ⊆ η.positiveHalfSpace ∪ η.negativeHalfSpace := by
    intro z hz
    exact (complement_mem_halfSpace (hcomp hz) hη).elim Or.inl Or.inr
    have := hS.subset_left_of_subset_union (positiveHalfSpace_isOpen η)
      (negativeHalfSpace_isOpen η) (halfSpaces_disjoint η) hS_sub ⟨x, hx, hxp⟩
    exact hyp (this hy)

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[connected_subset_in_negative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma connected_subset_in_negative
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {S : Set E}
  {η : AffineHyperplane E}
  {x : E}
-- given
  (hS : IsPreconnected S)
  (hcomp : S ⊆ arr.complement)
  (hη : η ∈ arr.hyperplanes)
  (hx : x ∈ S)
  (hxn : x ∈ η.negativeHalfSpace) :
-- imply
  S ⊆ η.negativeHalfSpace := by
-- proof
  intro y hy
  by_contra hyp
  have hy_comp := hcomp hy
  obtain h | h := complement_mem_halfSpace hy_comp hη
  · have hS_sub : S ⊆ η.positiveHalfSpace ∪ η.negativeHalfSpace := by
    intro z hz
    exact (complement_mem_halfSpace (hcomp hz) hη).elim Or.inl Or.inr
    have := hS.subset_right_of_subset_union (positiveHalfSpace_isOpen η)
      (negativeHalfSpace_isOpen η) (halfSpaces_disjoint η) hS_sub ⟨x, hx, hxn⟩
    exact hyp (this hy)
  · exact hyp h

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[chamber_subset_halfSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma chamber_subset_halfSpace
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {C : arr.Chamber}
  {η : AffineHyperplane E}
-- given
  (hη : η ∈ arr.hyperplanes) :
-- imply
  C.set ⊆ η.positiveHalfSpace ∨ C.set ⊆ η.negativeHalfSpace := by
-- proof
  obtain ⟨⟨x, hx⟩, _⟩ := C.isConnected
  have hx_comp := C.subset_complement hx
  obtain hxp | hxn := complement_mem_halfSpace hx_comp hη
  · left
    exact connected_subset_in_positive C.isConnected.isPreconnected C.subset_complement hη hx hxp
  · right
    exact connected_subset_in_negative C.isConnected.isPreconnected C.subset_complement hη hx hxn

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[sameSide_or_separated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma sameSide_or_separated
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {C D : arr.Chamber}
  {η : AffineHyperplane E}
-- given
  (hη : η ∈ arr.hyperplanes) :
-- imply
  SameSide η hη C D ∨ SeparatesChambers η hη C D := by
-- proof
  obtain hC | hC <;> := chamber_subset_halfSpace C hη
  obtain hD | hD := chamber_subset_halfSpace D hη
  · left; left; exact ⟨hC, hD⟩
  · right; left; exact ⟨hC, hD⟩
  · right; right; exact ⟨hC, hD⟩
  · left; right; exact ⟨hC, hD⟩

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[mem_chamber_of_same_signs](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma mem_chamber_of_same_signs
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {C : arr.Chamber}
  {x : E}
-- given
  (_hx : x ∈ arr.complement)
  (hsigns : ∀ η ∈ arr.hyperplanes, (C.set ⊆ η.positiveHalfSpace → x ∈ η.positiveHalfSpace) ∧ (C.set ⊆ η.negativeHalfSpace → x ∈ η.negativeHalfSpace)) :
-- imply
  x ∈ C.set := by
-- proof
  by_contra hxC
  obtain ⟨⟨y, hy⟩, hconn⟩ := C.isConnected
  have hy_comp := C.subset_complement hy
  have hseg_comp : segment ℝ y x ⊆ arr.complement := by
    intro z hz
    simp only [complement, Set.mem_diff, Set.mem_univ, true_and, unionSet]
    intro habs
    simp only [Set.mem_iUnion] at habs
    obtain ⟨η, hη_mem, hz_η⟩ := habs
    obtain hC_pos | hC_neg := chamber_subset_halfSpace C hη_mem
    · have hy_pos := hC_pos hy
      have hx_pos := (hsigns η hη_mem).1 hC_pos
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
      have hz_pos := HalfSpaceConvex η hy_pos hx_pos ha hb hab
      simp only [AffineHyperplane.positiveHalfSpace, Set.mem_setOf_eq] at hz_pos
      simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hz_η
      linarith
    · have hy_neg := hC_neg hy
      have hx_neg := (hsigns η hη_mem).2 hC_neg
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
      have hz_neg := negativeHalfSpace_convex η hy_neg hx_neg ha hb hab
      simp only [AffineHyperplane.negativeHalfSpace, Set.mem_setOf_eq] at hz_neg
      simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hz_η
      linarith
  have hseg_conn : IsConnected (segment ℝ y x) :=
    (convex_segment y x).isConnected ⟨y, left_mem_segment ℝ y x⟩
  have hy_in_seg : y ∈ segment ℝ y x := left_mem_segment ℝ y x
  have hunion_conn : IsConnected (C.set ∪ segment ℝ y x) := by
    constructor
    · exact ⟨y, Or.inl hy⟩
    · exact IsPreconnected.union y hy hy_in_seg hconn hseg_conn.isPreconnected
  have hunion_comp : C.set ∪ segment ℝ y x ⊆ arr.complement :=
    Set.union_subset C.subset_complement hseg_comp
  have := C.is_maximal (C.set ∪ segment ℝ y x) hunion_comp hunion_conn Set.subset_union_left
  have hx_in_union : x ∈ C.set ∪ segment ℝ y x :=
    Set.mem_union_right _ (right_mem_segment ℝ y x)
  exact hxC (this hx_in_union)

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[chambers_eq_of_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma chambers_eq_of_sameSide
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {C D : arr.Chamber}
-- given
  (hsame : ∀ η ∈ arr.hyperplanes, ∀ hη : η ∈ arr.hyperplanes, SameSide η hη C D) :
-- imply
  C.set = D.set := by
-- proof
  apply Set.Subset.antisymm
  ·
    intro c hc
    have hc_comp := C.subset_complement hc
    apply mem_chamber_of_same_signs D hc_comp
    intro η hη_mem
    have hside := hsame η hη_mem hη_mem
    constructor
    · intro hD_pos
      obtain ⟨hC_pos, _⟩ | ⟨hC_neg, hD_neg⟩ := hside
      · exact hC_pos hc
      ·
        obtain ⟨⟨d, hd⟩, _⟩ := D.isConnected
        have := hD_pos hd
        have := hD_neg hd
        simp only [AffineHyperplane.positiveHalfSpace, AffineHyperplane.negativeHalfSpace,
          Set.mem_setOf_eq] at *
        linarith
    · intro hD_neg
      obtain ⟨hC_pos, hD_pos⟩ | ⟨hC_neg, _⟩ := hside
      · obtain ⟨⟨d, hd⟩, _⟩ := D.isConnected
        have := hD_pos hd
        have := hD_neg hd
        simp only [AffineHyperplane.positiveHalfSpace, AffineHyperplane.negativeHalfSpace,
          Set.mem_setOf_eq] at *
        linarith
      · exact hC_neg hc
  ·
    intro d hd
    have hd_comp := D.subset_complement hd
    apply mem_chamber_of_same_signs C hd_comp
    intro η hη_mem
    have hside := hsame η hη_mem hη_mem
    constructor
    · intro hC_pos
      obtain ⟨_, hD_pos⟩ | ⟨hC_neg, _⟩ := hside
      · exact hD_pos hd
      · obtain ⟨⟨c, hc⟩, _⟩ := C.isConnected
        have := hC_pos hc
        have := hC_neg hc
        simp only [AffineHyperplane.positiveHalfSpace, AffineHyperplane.negativeHalfSpace,
          Set.mem_setOf_eq] at *
        linarith
    · intro hC_neg
      obtain ⟨hC_pos, _⟩ | ⟨_, hD_neg⟩ := hside
      · obtain ⟨⟨c, hc⟩, _⟩ := C.isConnected
        have := hC_pos hc
        have := hC_neg hc
        simp only [AffineHyperplane.positiveHalfSpace, AffineHyperplane.negativeHalfSpace,
          Set.mem_setOf_eq] at *
        linarith
      · exact hD_neg hd
end HyperplaneArrangement
/-- *The first hyperplane crossed by a path from $C$ to $D$ is a wall of $C$*: for two
distinct chambers in a locally finite arrangement, there exists a hyperplane $η$ that is both
a wall of $C$ and separates $C$ from $D$. This is the geometric heart of producing walls from
distinctness. (Currently this theorem is left as `sorry`.) -/
namespace HyperplaneArrangement

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[chamber_not_both_sides](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma chamber_not_both_sides
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {C : arr.Chamber}
  {η : AffineHyperplane E}
-- given
  (hpos : C.set ⊆ η.positiveHalfSpace)
  (hneg : C.set ⊆ η.negativeHalfSpace) :
-- imply
  False := by
-- proof
  obtain ⟨⟨c, hc⟩, _⟩ := C.isConnected
  have := hpos hc
  have := hneg hc
  simp only [AffineHyperplane.positiveHalfSpace, AffineHyperplane.negativeHalfSpace,
    Set.mem_setOf_eq] at *
  linarith

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[adjacent_separated_by_unique_wall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma adjacent_separated_by_unique_wall
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {C D : arr.Chamber}
  {η : AffineHyperplane E}
  {hη : η ∈ arr.hyperplanes}
  {ξ : AffineHyperplane E}
  {hξ : ξ ∈ arr.hyperplanes}
-- given
  (hadj : AdjacentAlong C D η hη)
  (hsep : SeparatesChambers ξ hξ C D) :
-- imply
  ξ = η := by
-- proof
  by_contra hne
  obtain ⟨_, _, hsame⟩ := hadj
  have := hsame ξ hξ hne hξ
  obtain ⟨hC_pos, hD_pos⟩ | ⟨hC_neg, hD_neg⟩ <;> := this
  obtain ⟨hCp, hDn⟩ | ⟨hCn, hDp⟩ := hsep
  · exact chamber_not_both_sides D hD_pos hDn
  · exact chamber_not_both_sides C hC_pos hCn
  · exact chamber_not_both_sides C hCp hC_neg
  · exact chamber_not_both_sides D hDp hD_neg

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[exactly_one_wall_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma exactly_one_wall_adjacent
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {C D : arr.Chamber}
  {η : AffineHyperplane E}
  {hη : η ∈ arr.hyperplanes}
-- given
  (hne : C.set ≠ D.set)
  (hsep : SeparatesChambers η hη C D)
  (huniq : ∀ ξ ∈ arr.hyperplanes, ∀ hξ : ξ ∈ arr.hyperplanes, SeparatesChambers ξ hξ C D → ξ = η) :
-- imply
  AdjacentAlong C D η hη := by
-- proof
  refine ⟨hne, hsep, ?_⟩
  intro ξ hξ_mem hξ_ne hξ
  have hξ_not_sep : ¬ SeparatesChambers ξ hξ C D := by
    intro h
    exact hξ_ne (huniq ξ hξ_mem hξ h)
  obtain hsame | hsep' := sameSide_or_separated C D hξ
  · exact hsame
  · exact absurd hsep' hξ_not_sep

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[carrier_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma carrier_isClosed
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {η : AffineHyperplane E} :
-- imply
  IsClosed η.carrier :=
-- proof
  isClosed_eq (continuous_const.inner continuous_id) continuous_const

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[complement_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma complement_isOpen
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
-- given
  (hlf : arr.IsLocallyFinite) :
-- imply
  IsOpen arr.complement := by
-- proof
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx_not : x ∉ arr.unionSet := by
    simp only [complement, Set.mem_diff, Set.mem_univ, true_and] at hx; exact hx
  obtain ⟨ε, hε, hfin⟩ := hlf x
  set S := {h ∈ arr.hyperplanes | (Metric.ball x ε ∩ h.carrier).Nonempty} with hS_def
  have hS_compl_nhds : ∀ h ∈ S, (h.carrier)ᶜ ∈ nhds x := by
    intro h hh
    have hh_mem : h ∈ arr.hyperplanes := hh.1
    have hx_not_carrier : x ∉ h.carrier := by
      intro habs
      exact hx_not (Set.mem_biUnion hh_mem habs)
    exact (carrier_isClosed h).compl_mem_nhds hx_not_carrier
  have hinter_nhds : (⋂ h ∈ S, (h.carrier)ᶜ) ∈ nhds x :=
    (Filter.biInter_mem hfin).mpr hS_compl_nhds
  have hball_nhds : Metric.ball x ε ∈ nhds x := Metric.ball_mem_nhds x hε
  have hT_nhds : Metric.ball x ε ∩ (⋂ h ∈ S, (h.carrier)ᶜ) ∈ nhds x :=
    Filter.inter_mem hball_nhds hinter_nhds
  apply Filter.mem_of_superset hT_nhds
  intro y ⟨hy_ball, hy_inter⟩
  simp only [complement, Set.mem_diff, Set.mem_univ, true_and, unionSet]
  intro hy_union
  rw [Set.mem_iUnion₂] at hy_union
  obtain ⟨h, hh_mem, hy_carrier⟩ := hy_union
  by_cases hh_S : h ∈ S
  ·
    have := Set.mem_iInter₂.mp hy_inter h hh_S
    exact this hy_carrier
  ·
    have : ¬(Metric.ball x ε ∩ h.carrier).Nonempty := by
      intro hne
      exact hh_S ⟨hh_mem, hne⟩
    exact this ⟨y, hy_ball, hy_carrier⟩

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[chamber_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean)
-/
@[path]
lemma chamber_isOpen
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {C : arr.Chamber}
-- given
  (hlf : arr.IsLocallyFinite) :
-- imply
  IsOpen C.set := by
-- proof
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hopen := complement_isOpen hlf
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x (C.subset_complement hx)
  have hball_conn : IsConnected (Metric.ball x r) :=
    (convex_ball x r).isConnected ⟨x, Metric.mem_ball_self hr⟩
  have hunion_conn : IsConnected (C.set ∪ Metric.ball x r) := by
    constructor
    · exact ⟨x, Or.inl hx⟩
    · exact IsPreconnected.union x hx (Metric.mem_ball_self hr)
      C.isConnected.isPreconnected hball_conn.isPreconnected
  have hunion_comp : C.set ∪ Metric.ball x r ⊆ arr.complement :=
    Set.union_subset C.subset_complement hball
  have hball_sub : Metric.ball x r ⊆ C.set := fun y hy =>
    C.is_maximal _ hunion_comp hunion_conn Set.subset_union_left (Or.inr hy)
  exact ⟨Metric.ball x r, hball_sub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩

end HyperplaneArrangement


-- created on 2026-10-23
