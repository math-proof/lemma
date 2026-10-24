import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.AffineWeylBook
open Set AffineReflectionGroup AffineWeylGroup AffineWeylGroupData
open scoped InnerProductSpace


namespace AffineReflectionGroup

/--
[translation_subgroup_discrete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma translation_subgroup_discrete
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {C : W.Alcove}
-- given
  (hC_open : IsOpen C.set)
  (hC_nonempty : C.set.Nonempty)
  (hdisjoint : ∀ w ∈ W.TranslationSubgroup, w ≠ 1 → Disjoint C.set ((w : AffineIsometryEquiv ℝ E E) '' C.set))
  (htransl : ∀ w ∈ W.TranslationSubgroup, ∀ y : E, (w : AffineIsometryEquiv ℝ E E) y = y + (w : AffineIsometryEquiv ℝ E E) 0) :
-- imply
  ∃ ε > 0, ∀ w ∈ W.TranslationSubgroup, w ≠ 1 → ‖((w : AffineIsometryEquiv ℝ E E) 0 : E)‖ ≥ ε := by
-- proof
  obtain ⟨x0, hx0⟩ := hC_nonempty
  obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp hC_open x0 hx0
  refine ⟨ε, hε_pos, ?_⟩
  intro w hw hw_ne
  by_contra h_small
  push Not at h_small
  have h_wx0 : (w : AffineIsometryEquiv ℝ E E) x0 ∈ Metric.ball x0 ε := by
    rwa [Metric.mem_ball, dist_eq_norm, htransl w hw x0, add_sub_cancel_left]
  exact Set.disjoint_iff.mp (hdisjoint w hw hw_ne)
    ⟨hball h_wx0, x0, hx0, rfl⟩

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[exists_compact_fundamental_domain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma exists_compact_fundamental_domain
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {C : W.Alcove}
-- given
  (hWbar_finite : Set.Finite W.LinearPartGroup.carrier)
  (hC_compact : IsCompact (closure C.set))
  (hcovers_W : ∀ x : E, ∃ w ∈ W.group, ((w : AffineIsometryEquiv ℝ E E)⁻¹) x ∈ closure C.set)
  (hgen : ∀ wbar ∈ W.LinearPartGroup, ∃ g ∈ W.Stabilizer 0, linearPartHom g = wbar)
  (hx : W.SpecialPoint (0 : E)) :
-- imply
  ∃ Y : Set E, IsCompact Y ∧ (∀ x : E, ∃ w ∈ W.TranslationSubgroup, ((w : AffineIsometryEquiv ℝ E E)⁻¹) x ∈ Y) := by
-- proof
  set Y := ⋃ wbar ∈ W.LinearPartGroup,
    (fun v => (wbar : LinearIsometryEquiv (RingHom.id ℝ) E E) v) '' closure C.set
  refine ⟨Y, ?_, ?_⟩
  · exact hWbar_finite.isCompact_biUnion (fun wbar _ =>
    hC_compact.image (wbar : LinearIsometryEquiv (RingHom.id ℝ) E E).continuous)
  · intro x
    obtain ⟨w, hw, hw_inv⟩ := hcovers_W x
    obtain ⟨t, ht, s, hs, hws⟩ :=
      W.semidirect_product_decomposition 0 hx hgen w hw
    refine ⟨t, ht, ?_⟩
    have h_eq : ((t : AffineIsometryEquiv ℝ E E)⁻¹) x = (s : AffineIsometryEquiv ℝ E E) (((w : AffineIsometryEquiv ℝ E E)⁻¹) x) := by
      have hinv : (w : AffineIsometryEquiv ℝ E E)⁻¹ = (s : AffineIsometryEquiv ℝ E E)⁻¹ * (t : AffineIsometryEquiv ℝ E E)⁻¹ := by
        rw [hws]; group
      show (t : AffineIsometryEquiv ℝ E E)⁻¹ x = s (((w : AffineIsometryEquiv ℝ E E)⁻¹) x)
      rw [hinv]
      show (t : AffineIsometryEquiv ℝ E E)⁻¹ x =
        (s : AffineIsometryEquiv ℝ E E) ((s : AffineIsometryEquiv ℝ E E)⁻¹ ((t : AffineIsometryEquiv ℝ E E)⁻¹ x))
      rw [show (s : AffineIsometryEquiv ℝ E E) ((s : AffineIsometryEquiv ℝ E E)⁻¹ ((t : AffineIsometryEquiv ℝ E E)⁻¹ x)) =
        ((s * s⁻¹ : AffineIsometryEquiv ℝ E E)) ((t : AffineIsometryEquiv ℝ E E)⁻¹ x) from rfl]
      simp
    rw [h_eq]
    have hs_fix : (s : AffineIsometryEquiv ℝ E E) (0 : E) = 0 := hs.2
    have hs_lin : linearPartHom s ∈ W.LinearPartGroup :=
      ⟨s, W.stabilizer_le_group 0 hs, rfl⟩
    suffices hsact : (s : AffineIsometryEquiv ℝ E E) (((w : AffineIsometryEquiv ℝ E E)⁻¹) x) =
      (linearPartHom s : LinearIsometryEquiv (RingHom.id ℝ) E E) (((w : AffineIsometryEquiv ℝ E E)⁻¹) x) by
      rw [hsact]
      exact Set.mem_biUnion hs_lin ⟨((w : AffineIsometryEquiv ℝ E E)⁻¹) x, hw_inv, rfl⟩
    have h_diff := AffineIsometryEquiv.map_vsub s
      (((w : AffineIsometryEquiv ℝ E E)⁻¹) x) (0 : E)
    simp only [vsub_eq_sub, sub_zero] at h_diff
    rwa [hs_fix, sub_zero] at h_diff

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[exists_compact_fundamental_domain_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma exists_compact_fundamental_domain_unconditional
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {C : W.Alcove}
-- given
  (hWbar_finite : Set.Finite W.LinearPartGroup.carrier)
  (hC_compact : IsCompact (closure C.set))
  (hcovers_W : ∀ x : E, ∃ w ∈ W.group, ((w : AffineIsometryEquiv ℝ E E)⁻¹) x ∈ closure C.set)
  (hx : W.SpecialPoint (0 : E)) :
-- imply
  ∃ Y : Set E, IsCompact Y ∧ (∀ x : E, ∃ w ∈ W.TranslationSubgroup, ((w : AffineIsometryEquiv ℝ E E)⁻¹) x ∈ Y) :=
-- proof
  W.exists_compact_fundamental_domain C hWbar_finite hC_compact hcovers_W
    (W.stabilizer_surjects_unconditional 0 hx) hx

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[translation_acts_additively](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma translation_acts_additively
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {w : AffineIsometryEquiv ℝ E E}
  {y : E}
-- given
  (hw : w ∈ W.TranslationSubgroup) :
-- imply
  (w : AffineIsometryEquiv ℝ E E) y = y + (w : AffineIsometryEquiv ℝ E E) 0 := by
-- proof
  have hw_ker : w ∈ linearPartHom.ker := hw.2
  rw [MonoidHom.mem_ker] at hw_ker
  have h_diff := AffineIsometryEquiv.map_vsub w y (0 : E)
  simp only [vsub_eq_sub, sub_zero] at h_diff
  have h_lin : (AffineIsometryEquiv.linearIsometryEquiv w) y = y := by
    have : (AffineIsometryEquiv.linearIsometryEquiv w) = (1 : LinearIsometryEquiv (RingHom.id ℝ) E E) := hw_ker
    simp [this]
  rw [h_lin] at h_diff
  exact eq_add_of_sub_eq h_diff.symm

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[alcove_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma alcove_nonempty
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {C : W.Alcove} :
-- imply
  C.set.Nonempty :=
-- proof
  C.isConnected.nonempty

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[alcove_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma alcove_exists
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
-- given
  (hess : W.IsEssential)
  (hind : W.IsIndecomposable) :
-- imply
  Nonempty W.Alcove := by
-- proof
  have h_carrier_closed : ∀ h : AffineHyperplane E, IsClosed h.carrier :=
    fun h => isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have h_carrier_interior : ∀ h : AffineHyperplane E, interior h.carrier = ∅ := by
    intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
    obtain ⟨r, hr_pos, hr_sub⟩ := hx
    have hn_ne : h.normal ≠ 0 := h.normal_ne_zero
    have hn_pos : 0 < ‖h.normal‖ := norm_pos_iff.mpr hn_ne
    set y := x + (r / (2 * ‖h.normal‖)) • h.normal
    have hy_ball : y ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [y, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hr_pos (mul_pos two_pos hn_pos))]
      field_simp; linarith
    have hy_carrier : y ∉ h.carrier := by
      simp only [AffineHyperplane.carrier, Set.mem_setOf_eq, y]
      rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
      have hx_on : ⟪h.normal, x⟫_ℝ = h.offset := by
        have := hr_sub (Metric.mem_ball_self hr_pos)
        simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at this
        exact this
      rw [hx_on]
      intro heq
      have h1 : r / (2 * ‖h.normal‖) > 0 := div_pos hr_pos (mul_pos two_pos hn_pos)
      have h2 : ‖h.normal‖ ^ 2 > 0 := pow_pos hn_pos 2
      linarith [mul_pos h1 h2]
    exact hy_carrier (hr_sub hy_ball)
  obtain ⟨ε, hε_pos, hS_fin⟩ := W.locallyFinite 0
  set S := {h ∈ W.arrangement.hyperplanes | (Metric.ball 0 ε ∩ h.carrier).Nonempty}
  have hS_union_closed : IsClosed (⋃ h ∈ S, h.carrier) :=
    hS_fin.isClosed_biUnion (fun h _ => h_carrier_closed h)
  have hS_union_interior : interior (⋃ h ∈ S, h.carrier) = ∅ := by
    classical
    set T := hS_fin.toFinset
    have hST : S = ↑T := (Set.Finite.coe_toFinset hS_fin).symm
    rw [hST]
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.coe_insert, Set.biUnion_insert, Set.eq_empty_iff_forall_notMem]
      intro x hx
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
      obtain ⟨r, hr_pos, hr_sub⟩ := hx
      have ha_dense : Dense a.carrierᶜ := by
        rw [← interior_eq_empty_iff_dense_compl]; exact h_carrier_interior a
      have h_rest_dense : Dense (⋃ h ∈ (s : Set (AffineHyperplane E)), h.carrier)ᶜ := by
        rw [← interior_eq_empty_iff_dense_compl]; exact ih
      have hU_open : IsOpen (Metric.ball x r ∩ a.carrierᶜ) :=
        Metric.isOpen_ball.inter (h_carrier_closed a).isOpen_compl
      obtain ⟨z, hz_ball, hz_not_a⟩ := ha_dense.inter_open_nonempty
        (Metric.ball x r) Metric.isOpen_ball ⟨x, Metric.mem_ball_self hr_pos⟩
      obtain ⟨w, ⟨hw_ball, hw_not_a⟩, hw_not_rest⟩ := h_rest_dense.inter_open_nonempty
        (Metric.ball x r ∩ a.carrierᶜ) hU_open ⟨z, hz_ball, hz_not_a⟩
      obtain h | h := hr_sub hw_ball
      · exact hw_not_a h
      · exact hw_not_rest h
  have h_compl_ne : (Metric.ball (0 : E) ε \ ⋃ h ∈ S, h.carrier).Nonempty := by
    by_contra h_empty
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at h_empty
    have : Metric.ball (0 : E) ε ⊆ interior (⋃ h ∈ S, h.carrier) :=
      Metric.isOpen_ball.subset_interior_iff.mpr h_empty
    have h_ne : (interior (⋃ h ∈ S, h.carrier)).Nonempty :=
      ⟨0, this (Metric.mem_ball_self hε_pos)⟩
    rw [hS_union_interior] at h_ne
    exact Set.not_nonempty_empty h_ne
  obtain ⟨x₀, hx₀_ball, hx₀_not_S⟩ := h_compl_ne
  have hx₀_compl : x₀ ∈ W.arrangement.complement := by
    constructor
    · exact Set.mem_univ x₀
    · intro hx₀_union
      obtain ⟨h, hh_arr, hx₀_h⟩ := Set.mem_iUnion₂.mp hx₀_union
      have hh_S : h ∈ S := ⟨hh_arr, ⟨x₀, hx₀_ball, hx₀_h⟩⟩
      exact hx₀_not_S (Set.mem_biUnion hh_S hx₀_h)
  set F := W.arrangement.complement
  set CC := connectedComponentIn F x₀
  have hx₀_F : x₀ ∈ F := hx₀_compl
  exact ⟨{
    set := CC
    subset_complement := connectedComponentIn_subset F x₀
    isConnected := isConnected_connectedComponentIn_iff.mpr hx₀_F
    is_maximal := by
      intro S' hS'_sub hS'_conn hCC_sub
      have hx₀_S' : x₀ ∈ S' := hCC_sub (mem_connectedComponentIn hx₀_F)
      exact hS'_conn.isPreconnected.subset_connectedComponentIn hx₀_S' hS'_sub
  }⟩

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[alcove_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma alcove_isOpen
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {C : W.Alcove}
-- given
  (hess : W.IsEssential)
  (hind : W.IsIndecomposable) :
-- imply
  IsOpen C.set := by
-- proof
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hx_compl := C.subset_complement hx
  obtain ⟨ε₀, hε₀_pos, hfin⟩ := W.locallyFinite x
  have hx_not_on : ∀ h ∈ W.arrangement.hyperplanes, x ∉ h.carrier := by
    intro h hh habs
    have : x ∈ W.arrangement.unionSet := Set.mem_biUnion hh habs
    exact (hx_compl.2 this).elim
  have h_closed : ∀ h : AffineHyperplane E, IsClosed h.carrier := by
    intro h
    exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
  set S := {h ∈ W.arrangement.hyperplanes | (Metric.ball x ε₀ ∩ h.carrier).Nonempty}
  have hS_fin : S.Finite := hfin
  have h_S_union_closed : IsClosed (⋃ h ∈ S, h.carrier) := by
    exact hS_fin.isClosed_biUnion (fun h _ => h_closed h)
  have hx_not_in_S_union : x ∉ ⋃ h ∈ S, h.carrier := by
    intro habs
    obtain ⟨h, hh, hxh⟩ := Set.mem_iUnion₂.mp habs
    exact hx_not_on h hh.1 hxh
  obtain ⟨δ₁, hδ₁_pos, hδ₁_disj⟩ := Metric.nhds_basis_ball.mem_iff.mp
    (h_S_union_closed.isOpen_compl.mem_nhds (Set.mem_compl hx_not_in_S_union))
  set δ := min δ₁ ε₀ with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ₁_pos hε₀_pos
  have h_ball_compl : Metric.ball x δ ⊆ W.arrangement.complement := by
    intro z hz
    constructor
    · exact Set.mem_univ z
    · intro hz_union
      obtain ⟨h, hh_arr, hz_carrier⟩ := Set.mem_iUnion₂.mp hz_union
      have hz_ball_ε : z ∈ Metric.ball x ε₀ :=
        Metric.ball_subset_ball (min_le_right _ _) hz
      have hh_S : h ∈ S := ⟨hh_arr, ⟨z, hz_ball_ε, hz_carrier⟩⟩
      have hz_ball_δ₁ : z ∈ Metric.ball x δ₁ :=
        Metric.ball_subset_ball (min_le_left _ _) hz
      have hz_not_union : z ∉ ⋃ h ∈ S, h.carrier := hδ₁_disj hz_ball_δ₁
      exact hz_not_union (Set.mem_biUnion hh_S hz_carrier)
  have h_ball_conn : IsConnected (Metric.ball x δ) :=
    (convex_ball x δ).isConnected (Metric.nonempty_ball.mpr hδ_pos)
  have h_inter_ne : (C.set ∩ Metric.ball x δ).Nonempty :=
    ⟨x, hx, Metric.mem_ball_self hδ_pos⟩
  have h_union_conn : IsConnected (C.set ∪ Metric.ball x δ) :=
    IsConnected.union h_inter_ne C.isConnected h_ball_conn
  have h_union_compl : C.set ∪ Metric.ball x δ ⊆ W.arrangement.complement :=
    Set.union_subset C.subset_complement h_ball_compl
  refine ⟨Metric.ball x δ, ?_, Metric.isOpen_ball, Metric.mem_ball_self hδ_pos⟩
  exact fun y hy => C.is_maximal _ h_union_compl h_union_conn
    Set.subset_union_left (Set.subset_union_right hy)

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[translation_images_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma translation_images_disjoint
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {C : W.Alcove}
-- given
  (hess : W.IsEssential)
  (hind : W.IsIndecomposable) :
-- imply
  ∀ w ∈ W.TranslationSubgroup, w ≠ 1 → Disjoint C.set ((w : AffineIsometryEquiv ℝ E E) '' C.set) := by
-- proof
  intro w hw hw_ne
  have hw_group : w ∈ W.group := hw.1
  have g_maps_complement : ∀ (g : AffineIsometryEquiv ℝ E E), g ∈ W.group → ∀ x ∈ W.arrangement.complement,
    (g : AffineIsometryEquiv ℝ E E) x ∈ W.arrangement.complement := by
    intro g hg x hx
    simp only [HyperplaneArrangement.complement, Set.mem_diff, Set.mem_univ, true_and] at hx ⊢
    intro habs
    simp only [HyperplaneArrangement.unionSet, Set.mem_iUnion] at habs
    obtain ⟨η, hη_arr, hη_mem⟩ := habs
    obtain ⟨η', hη'_arr, hη'_eq⟩ := W.stable g⁻¹ (W.group.inv_mem hg) η hη_arr
    have h_ginv_gx : (g⁻¹ : AffineIsometryEquiv ℝ E E) (g x) = x := by
      show (g⁻¹ * g : AffineIsometryEquiv ℝ E E) x = x; rw [inv_mul_cancel]; rfl
    have : x ∈ η'.carrier := by rw [← h_ginv_gx]; exact (hη'_eq _).mpr hη_mem
    exact hx (Set.mem_iUnion₂.mpr ⟨η', hη'_arr, this⟩)
  have wC_sub : (w : AffineIsometryEquiv ℝ E E) '' C.set ⊆ W.arrangement.complement := by
    rintro _ ⟨y, hy, rfl⟩
    exact g_maps_complement w hw_group y (C.subset_complement hy)
  have wC_conn : IsConnected ((w : AffineIsometryEquiv ℝ E E) '' C.set) :=
    C.isConnected.image _ (AffineIsometryEquiv.continuous w).continuousOn
  have wC_max : ∀ S : Set E, S ⊆ W.arrangement.complement →
    IsConnected S → (w : AffineIsometryEquiv ℝ E E) '' C.set ⊆ S → S ⊆ (w : AffineIsometryEquiv ℝ E E) '' C.set := by
    intro S hS_comp hS_conn hS_sub
    have winvS_comp : (w⁻¹ : AffineIsometryEquiv ℝ E E) '' S ⊆ W.arrangement.complement := by
      rintro _ ⟨y, hy, rfl⟩
      exact g_maps_complement w⁻¹ (W.group.inv_mem hw_group) y (hS_comp hy)
    have winvS_conn : IsConnected ((w⁻¹ : AffineIsometryEquiv ℝ E E) '' S) :=
      hS_conn.image _ (AffineIsometryEquiv.continuous w⁻¹).continuousOn
    have hC_sub_winvS : C.set ⊆ (w⁻¹ : AffineIsometryEquiv ℝ E E) '' S := by
      intro y hy
      refine ⟨(w : AffineIsometryEquiv ℝ E E) y, hS_sub ⟨y, hy, rfl⟩, ?_⟩
      show (w⁻¹ * w : AffineIsometryEquiv ℝ E E) y = y; rw [inv_mul_cancel]; rfl
    have h_max := C.is_maximal _ winvS_comp winvS_conn hC_sub_winvS
    intro y hy
    have h_winv_y : (w⁻¹ : AffineIsometryEquiv ℝ E E) y ∈ C.set := h_max ⟨y, hy, rfl⟩
    refine ⟨(w⁻¹ : AffineIsometryEquiv ℝ E E) y, h_winv_y, ?_⟩
    show (w * w⁻¹ : AffineIsometryEquiv ℝ E E) y = y; rw [mul_inv_cancel]; rfl
  rw [Set.disjoint_iff]
  intro x ⟨hx_C, hx_wC⟩
  have h_inter_ne : (C.set ∩ (w : AffineIsometryEquiv ℝ E E) '' C.set).Nonempty := ⟨x, hx_C, hx_wC⟩
  have h_union_conn : IsConnected (C.set ∪ (w : AffineIsometryEquiv ℝ E E) '' C.set) :=
    C.isConnected.union h_inter_ne wC_conn
  have h_union_comp : C.set ∪ (w : AffineIsometryEquiv ℝ E E) '' C.set ⊆ W.arrangement.complement :=
    Set.union_subset C.subset_complement wC_sub
  have h_wC_sub_C : (w : AffineIsometryEquiv ℝ E E) '' C.set ⊆ C.set := fun y hy =>
    C.is_maximal _ h_union_comp h_union_conn Set.subset_union_left (Set.mem_union_right _ hy)
  have h_C_sub_wC : C.set ⊆ (w : AffineIsometryEquiv ℝ E E) '' C.set := fun y hy =>
    wC_max _ h_union_comp h_union_conn Set.subset_union_right (Set.mem_union_left _ hy)
  have h_eq : C.set = (w : AffineIsometryEquiv ℝ E E) '' C.set :=
    Set.Subset.antisymm h_C_sub_wC h_wC_sub_C
  have h_transl := W.translation_acts_additively w hw
  obtain ⟨n, vertices, hset, _⟩ := alcove_is_simplex W hess hind C
  have hC_bounded : Bornology.IsBounded C.set := by
    rw [hset]
    exact (isBounded_convexHull.mpr (Set.finite_range vertices).isBounded).subset interior_subset
  obtain ⟨x₀, hx₀⟩ := C.isConnected.nonempty
  set v := (w : AffineIsometryEquiv ℝ E E) (0 : E) with hv_def
  have h_iter : ∀ k : ℕ, x₀ + (k : ℝ) • v ∈ C.set := by
    intro k
    induction k with
    | zero => simp [hx₀]
    | succ k ih =>
      have : (w : AffineIsometryEquiv ℝ E E) (x₀ + (k : ℝ) • v) ∈ (w : AffineIsometryEquiv ℝ E E) '' C.set :=
        ⟨x₀ + (k : ℝ) • v, ih, rfl⟩
      rw [← h_eq] at this
      rw [h_transl (x₀ + (k : ℝ) • v)] at this
      convert this using 1
      push_cast
      rw [add_smul, one_smul]
      abel
  have h_v_eq_0 : v = 0 := by
    by_contra hv_ne
    have h_unbounded : ¬Bornology.IsBounded (Set.range (fun k : ℕ => x₀ + (k : ℝ) • v)) := by
      rw [Metric.isBounded_range_iff]
      push Not
      intro C_bound
      obtain ⟨k, hk⟩ := exists_nat_gt (C_bound / ‖v‖)
      refine ⟨0, k, ?_⟩
      simp only [Nat.cast_zero, zero_smul, add_zero]
      rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_natCast]
      calc C_bound < ↑k * ‖v‖ := by
        rwa [div_lt_iff₀ (norm_pos_iff.mpr hv_ne)] at hk
        _ ≤ ↑k * ‖v‖ := le_refl _
    exact h_unbounded (hC_bounded.subset (Set.range_subset_iff.mpr h_iter))
  exfalso; apply hw_ne
  ext y
  show (w : AffineIsometryEquiv ℝ E E) y = (1 : AffineIsometryEquiv ℝ E E) y
  rw [h_transl y, h_v_eq_0, add_zero]
  rfl

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[normalDirection_eq_of_smul_normal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma normalDirection_eq_of_smul_normal
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {η η' : AffineHyperplane E}
  {t : ℝ}
-- given
  (ht : t ≠ 0)
  (h : η'.normal = t • η.normal) :
-- imply
  normalDirection η' = normalDirection η := by
-- proof
  simp only [normalDirection]
  rw [h]
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 t ht) η.normal

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[stable_orthogonal_preserve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma stable_orthogonal_preserve
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {g : AffineIsometryEquiv ℝ E E}
  {η η' : AffineHyperplane E}
  {v : E}
-- given
  (hη'_eq : ∀ x : E, g x ∈ η'.carrier ↔ x ∈ η.carrier)
  (hv : @inner ℝ _ _ η.normal v = 0) :
-- imply
  @inner ℝ _ _ η'.normal ((AffineIsometryEquiv.linearIsometryEquiv g) v) = 0 := by
-- proof
  have hx₀ : ∃ x₀ : E, x₀ ∈ η.carrier := by
    use (η.offset / @inner ℝ _ _ η.normal η.normal) • η.normal
    simp only [AffineHyperplane.carrier, Set.mem_setOf_eq, inner_smul_right,
      real_inner_self_eq_norm_sq]
    rw [div_mul_cancel₀]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr η.normal_ne_zero)
  obtain ⟨x₀, hx₀_mem⟩ := hx₀
  set wbar := AffineIsometryEquiv.linearIsometryEquiv g with wbar_def
  have hgx₀ : g x₀ ∈ η'.carrier := (hη'_eq x₀).mpr hx₀_mem
  have hxv : x₀ + v ∈ η.carrier := by
    simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hx₀_mem ⊢
    rw [inner_add_right, hv, add_zero]; exact hx₀_mem
  have hgxv : g (x₀ + v) ∈ η'.carrier := (hη'_eq (x₀ + v)).mpr hxv
  have hg_add : g (x₀ + v) = g x₀ + wbar v := by
    have h := AffineIsometryEquiv.map_vsub g (x₀ + v) x₀
    simp only [vsub_eq_sub, add_sub_cancel_left] at h
    have : g (x₀ + v) - g x₀ = wbar v := by
      rw [← vsub_eq_sub]; exact h.symm
    rw [← this]; abel
  rw [hg_add] at hgxv
  simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hgx₀ hgxv
  rw [inner_add_right] at hgxv; linarith

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[mem_span_singleton_of_orthogonal_implication](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma mem_span_singleton_of_orthogonal_implication
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {a b : E}
-- given
  (ha : a ≠ 0)
  (h : ∀ v : E, @inner ℝ _ _ a v = 0 → @inner ℝ _ _ b v = 0) :
-- imply
  b ∈ Submodule.span ℝ {a} := by
-- proof
  rw [Submodule.mem_span_singleton]
  use @inner ℝ _ _ b a / @inner ℝ _ _ a a
  have ha_sq_ne : @inner ℝ _ _ a a ≠ (0 : ℝ) := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
  set c := @inner ℝ _ _ b a / @inner ℝ _ _ a a
  set diff := b - c • a
  suffices h_zero : diff = 0 by rw [sub_eq_zero] at h_zero; exact h_zero.symm
  rw [← @inner_self_eq_zero ℝ]
  have h_diff_a : @inner ℝ _ _ diff a = 0 := by
    show @inner ℝ _ _ (b - c • a) a = 0
    rw [inner_sub_left, inner_smul_left, conj_trivial, div_mul_cancel₀ _ ha_sq_ne, sub_self]
  have h_a_diff : @inner ℝ _ _ a diff = 0 := by rw [real_inner_comm]; exact h_diff_a
  have h_b_diff : @inner ℝ _ _ b diff = 0 := h diff h_a_diff
  show @inner ℝ _ _ diff diff = 0
  rw [show diff = b - c • a from rfl, inner_sub_left, inner_smul_left, conj_trivial,
    h_b_diff, h_a_diff, mul_zero, sub_zero]

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[linearPart_permutes_normalDirections](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma linearPart_permutes_normalDirections
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {W : AffineReflectionGroup E}
  {wbar : LinearIsometryEquiv (RingHom.id ℝ) E E}
  {d : Submodule ℝ E}
-- given
  (hwbar : wbar ∈ W.LinearPartGroup)
  (hd : d ∈ normalDirection '' W.arrangement.hyperplanes) :
-- imply
  Submodule.map wbar.toLinearEquiv.toLinearMap d ∈ normalDirection '' W.arrangement.hyperplanes := by
-- proof
  obtain ⟨η, hη_arr, rfl⟩ := hd
  rw [AffineReflectionGroup.LinearPartGroup, Subgroup.mem_map] at hwbar
  obtain ⟨g, hg_mem, hg_eq⟩ := hwbar
  obtain ⟨η', hη'_arr, hη'_eq⟩ := W.stable g hg_mem η hη_arr
  refine ⟨η', hη'_arr, ?_⟩
  simp only [normalDirection, Submodule.map_span, Set.image_singleton]
  have hwbar_eq : AffineIsometryEquiv.linearIsometryEquiv g = wbar := by
    exact_mod_cast hg_eq
  have h1 : η'.normal ∈ Submodule.span ℝ ({(wbar.toLinearEquiv : E →ₗ[ℝ] E) η.normal} : Set E) := by
    apply mem_span_singleton_of_orthogonal_implication
    · intro h; exact η.normal_ne_zero (wbar.injective (by simp [show (wbar.toLinearEquiv : E →ₗ[ℝ] E) η.normal = wbar η.normal from rfl] at h; rw [h, map_zero]))
    · intro v hv
      have h_inv : @inner ℝ _ _ η.normal (wbar.symm v) = 0 := by
        have hi := LinearIsometryEquiv.inner_map_map wbar η.normal (wbar.symm v)
        simp [LinearIsometryEquiv.apply_symm_apply] at hi
        rw [← hi]; convert hv using 2
      have := stable_orthogonal_preserve g η η' hη'_eq (wbar.symm v) h_inv
      rw [hwbar_eq] at this
      simp [LinearIsometryEquiv.apply_symm_apply] at this
      exact this
  have h2 : (wbar.toLinearEquiv : E →ₗ[ℝ] E) η.normal ∈ Submodule.span ℝ ({η'.normal} : Set E) := by
    apply mem_span_singleton_of_orthogonal_implication
    · exact η'.normal_ne_zero
    · intro v hv
      suffices h_goal : @inner ℝ _ _ η.normal (wbar.symm v) = 0 by
        have hi := LinearIsometryEquiv.inner_map_map wbar η.normal (wbar.symm v)
        simp [LinearIsometryEquiv.apply_symm_apply] at hi
        have : (wbar.toLinearEquiv : E →ₗ[ℝ] E) η.normal = wbar η.normal := rfl
        rw [this, hi]; exact h_goal
      have hη_inv : ∀ x : E, (g⁻¹ : AffineIsometryEquiv ℝ E E) x ∈ η.carrier ↔ x ∈ η'.carrier := by
        intro x; constructor
        · intro hx
          have := (hη'_eq ((g⁻¹ : AffineIsometryEquiv ℝ E E) x)).mpr hx
          rwa [show (g : AffineIsometryEquiv ℝ E E) ((g⁻¹ : AffineIsometryEquiv ℝ E E) x) = x from by
            show (g * g⁻¹ : AffineIsometryEquiv ℝ E E) x = x; rw [mul_inv_cancel]; rfl] at this
        · intro hx; rw [← hη'_eq]
          show (g * g⁻¹ : AffineIsometryEquiv ℝ E E) x ∈ η'.carrier
          rw [mul_inv_cancel]; exact hx
      have h_lin_inv : AffineIsometryEquiv.linearIsometryEquiv g⁻¹ = wbar.symm := by
        have : linearPartHom g⁻¹ = (linearPartHom g)⁻¹ := map_inv linearPartHom g
        rw [hg_eq] at this
        ext v; show AffineIsometryEquiv.linearIsometryEquiv g⁻¹ v = wbar.symm v
        have hv := congr_fun (congr_arg (↑·) this) v
        simp only [LinearIsometryEquiv.coe_inv, linearPartHom, MonoidHom.coe_mk, OneHom.coe_mk] at hv
        exact hv
      have := stable_orthogonal_preserve g⁻¹ η' η hη_inv v hv
      rwa [h_lin_inv] at this
  apply le_antisymm
  · rw [Submodule.span_le, Set.singleton_subset_iff]; exact h1
  · rw [Submodule.span_le, Set.singleton_subset_iff]; exact h2

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[isometry_fixes_span_pm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma isometry_fixes_span_pm
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {wbar : LinearIsometryEquiv (RingHom.id ℝ) E E}
  {n : E}
-- given
  (hn : n ≠ 0)
  (h : Submodule.map wbar.toLinearEquiv.toLinearMap (Submodule.span ℝ {n}) = Submodule.span ℝ {n}) :
-- imply
  wbar n = n ∨ wbar n = -n := by
-- proof
  have hmem : wbar n ∈ Submodule.span ℝ ({n} : Set E) := by
    rw [← h]
    exact Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_singleton n))
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨a, ha⟩ := hmem
  have hnorm : ‖wbar n‖ = ‖n‖ := wbar.norm_map n
  rw [← ha, norm_smul, Real.norm_eq_abs] at hnorm
  have hn_pos : (0 : ℝ) < ‖n‖ := norm_pos_iff.mpr hn
  have ha_abs : |a| = 1 := by nlinarith [hn_pos]
  obtain h1 | h1 := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp ha_abs
  · left; rw [← ha, h1, one_smul]
  · right; rw [← ha, h1, neg_one_smul]

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[reflection_linearPart_fixes_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma reflection_linearPart_fixes_orthogonal
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {s : AffineIsometryEquiv ℝ E E}
  {η : AffineHyperplane E}
  {v : E}
-- given
  (hs_fix : ∀ y ∈ η.carrier, s y = y)
  (hs_inv : s * s = 1)
  (hv : @inner ℝ _ _ η.normal v = 0) :
-- imply
  (linearPartHom s : LinearIsometryEquiv (RingHom.id ℝ) E E) v = v := by
-- proof
  have ⟨x₀, hx₀⟩ : ∃ x₀ : E, x₀ ∈ η.carrier := by
    use (η.offset / @inner ℝ _ _ η.normal η.normal) • η.normal
    simp only [AffineHyperplane.carrier, Set.mem_setOf_eq, inner_smul_right,
      real_inner_self_eq_norm_sq]
    rw [div_mul_cancel₀]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr η.normal_ne_zero)
  have hxv : x₀ + v ∈ η.carrier := by
    simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hx₀ ⊢
    rw [inner_add_right, hv, add_zero]; exact hx₀
  have hs_x₀ : s x₀ = x₀ := hs_fix x₀ hx₀
  have hs_xv : s (x₀ + v) = x₀ + v := hs_fix (x₀ + v) hxv
  change AffineIsometryEquiv.linearIsometryEquiv s v = v
  have h := AffineIsometryEquiv.map_vsub s (x₀ + v) x₀
  simp only [vsub_eq_sub, add_sub_cancel_left] at h
  rw [h, hs_xv, hs_x₀, add_sub_cancel_left]

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[orthogonal_to_normals_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma orthogonal_to_normals_eq_zero
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {w : E}
-- given
  (hess : W.IsEssential)
  (hw : ∀ η ∈ W.arrangement.hyperplanes, @inner ℝ _ _ η.normal w = 0) :
-- imply
  w = 0 := by
-- proof
  apply hess w
  intro wbar hwbar_mem
  rw [AffineReflectionGroup.LinearPartGroup, Subgroup.mem_map] at hwbar_mem
  obtain ⟨g, hg_mem, hg_eq⟩ := hwbar_mem
  rw [W.generated_by_reflections] at hg_mem
  suffices h_refl : ∀ s, s ∈ Subgroup.closure
    {s | s ∈ W.group ∧ ∃ η ∈ W.arrangement.hyperplanes,
      (∀ y ∈ η.carrier, s y = y) ∧ s * s = 1} →
    (linearPartHom s : LinearIsometryEquiv (RingHom.id ℝ) E E) w = w by
    have := h_refl g hg_mem
    show wbar w = w
    rw [← hg_eq]; exact this
  apply Subgroup.closure_induction
  · intro s hs
    obtain ⟨_, η, hη, hs_fix, hs_inv⟩ := hs
    have hv_orth : @inner ℝ _ _ η.normal w = 0 := hw η hη
    exact reflection_linearPart_fixes_orthogonal s η hs_fix hs_inv w hv_orth
  ·
    rfl
  · intro s₁ s₂ _ _ ih₁ ih₂
    simp only [map_mul, LinearIsometryEquiv.coe_mul] at ih₁ ih₂ ⊢
    rw [Function.comp_apply, ih₂, ih₁]
  · intro s _ ih
    have hinv : linearPartHom s⁻¹ = (linearPartHom s)⁻¹ := map_inv linearPartHom s
    simp only [hinv, LinearIsometryEquiv.coe_inv]
    have := congr_arg (linearPartHom s).symm ih
    simp only [LinearIsometryEquiv.symm_apply_apply] at this
    exact this.symm

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[inner_eq_zero_of_different_signs](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma inner_eq_zero_of_different_signs
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {wbar : LinearIsometryEquiv (RingHom.id ℝ) E E}
  {n₁ n₂ : E}
  {ε₁ ε₂ : ℝ}
-- given
  (h0 : wbar n₁ = ε₁ • n₁)
  (h1 : wbar n₂ = ε₂ • n₂)
  (hne : ε₁ ≠ ε₂)
  (hε1 : ε₁ = 1 ∨ ε₁ = -1)
  (hε2 : ε₂ = 1 ∨ ε₂ = -1) :
-- imply
  @inner ℝ _ _ n₁ n₂ = 0 := by
-- proof
  have preserve := LinearIsometryEquiv.inner_map_map wbar n₁ n₂
  rw [h1, h2] at preserve
  simp only [inner_smul_left, inner_smul_right, conj_trivial] at preserve
  have hprod : ε₁ * ε₂ = -1 := by
    obtain rfl | rfl <;> rcases hε2 with rfl | rfl <;> simp at hne ⊢ := hε1
  have : ε₂ * (ε₁ * @inner ℝ _ _ n₁ n₂) = (ε₁ * ε₂) * @inner ℝ _ _ n₁ n₂ := by ring
  rw [this, hprod] at preserve
  linarith

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[linearIsometryEquiv_fixes_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma linearIsometryEquiv_fixes_orthogonal
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {s : AffineIsometryEquiv ℝ E E}
  {η : AffineHyperplane E}
  {v : E}
-- given
  (hfix : ∀ y ∈ η.carrier, s y = y)
  (hv : @inner ℝ _ _ η.normal v = 0) :
-- imply
  s.linearIsometryEquiv v = v := by
-- proof
  have hp := η.basePoint_mem_carrier
  have hpv : η.basePoint + v ∈ η.carrier := by
    simp only [AffineHyperplane.carrier, Set.mem_setOf_eq, inner_add_right, hv, add_zero]
    exact hp
  have key : s.linearIsometryEquiv v = s (η.basePoint + v) -ᵥ s η.basePoint := by
    rw [← AffineIsometryEquiv.map_vsub s (η.basePoint + v) η.basePoint]
    simp [vsub_eq_sub, add_sub_cancel_left]
  rw [key, hfix _ hpv, hfix _ hp]
  simp [vsub_eq_sub, add_sub_cancel_left]

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[affineIsometryEquiv_eq_linear_sub_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma affineIsometryEquiv_eq_linear_sub_add
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {s : AffineIsometryEquiv ℝ E E}
  {p x : E}
-- given
  (hp : s p = p) :
-- imply
  s x = s.linearIsometryEquiv (x - p) + p := by
-- proof
  have h := AffineIsometryEquiv.map_vsub s x p
  change s.linearIsometryEquiv (x -ᵥ p) = s x -ᵥ s p at h
  rw [vsub_eq_sub, vsub_eq_sub, hp] at h
  rw [h]; abel

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[inner_affineIsometry_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma inner_affineIsometry_eq
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {s : AffineIsometryEquiv ℝ E E}
  {η η' : AffineHyperplane E}
  {x : E}
-- given
  (hfix : ∀ y ∈ η'.carrier, s y = y)
  (horth : @inner ℝ _ _ η.normal η'.normal = 0) :
-- imply
  @inner ℝ _ _ η.normal (s x) = @inner ℝ _ _ η.normal x := by
-- proof
  have hLn : s.linearIsometryEquiv η.normal = η.normal :=
    linearIsometryEquiv_fixes_orthogonal s η' hfix η.normal
      (real_inner_comm η'.normal η.normal ▸ horth)
  have hinner_L (y : E) : @inner ℝ _ _ η.normal (s.linearIsometryEquiv y) =
    @inner ℝ _ _ η.normal y := by
    conv_lhs => rw [← hLn]; exact LinearIsometryEquiv.inner_map_map _ _ _
  have hp := hfix _ η'.basePoint_mem_carrier
  rw [affineIsometryEquiv_eq_linear_sub_add s η'.basePoint x hp,
    inner_add_right, hinner_L, inner_sub_right]
  linarith

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[affineIsometryEquiv_add_diff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma affineIsometryEquiv_add_diff
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {s : AffineIsometryEquiv ℝ E E}
  {x y : E}
-- given
  (hfix : s.linearIsometryEquiv (y - x) = y - x) :
-- imply
  s y = s x + (y - x) := by
-- proof
  have h := AffineIsometryEquiv.map_vsub s y x
  change s.linearIsometryEquiv (y -ᵥ x) = s y -ᵥ s x at h
  rw [vsub_eq_sub, vsub_eq_sub, hfix] at h
  rw [h]; abel

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[affine_reflections_commute_of_orthogonal_normals](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma affine_reflections_commute_of_orthogonal_normals
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {s₁ s₂ : AffineIsometryEquiv ℝ E E}
  {η₁ η₂ : AffineHyperplane E}
-- given
  (h₁_fix : ∀ y ∈ η₁.carrier, s₁ y = y)
  (h₁_inv : s₁ * s₁ = 1)
  (h₂_fix : ∀ y ∈ η₂.carrier, s₂ y = y)
  (h₂_inv : s₂ * s₂ = 1)
  (horth : @inner ℝ _ _ η₁.normal η₂.normal = 0) :
-- imply
  s₁ * s₂ = s₂ * s₁ := by
-- proof
  ext x
  simp only [AffineIsometryEquiv.coe_mul, Function.comp_apply]
  have horth' : @inner ℝ _ _ η₂.normal η₁.normal = 0 := by
    rw [real_inner_comm]; exact horth
  have hL₁ : s₁.linearIsometryEquiv (s₂ x - x) = s₂ x - x :=
    linearIsometryEquiv_fixes_orthogonal s₁ η₁ h₁_fix (s₂ x - x)
      (by rw [inner_sub_right]; linarith [inner_affineIsometry_eq s₂ η₁ η₂ h₂_fix horth x])
  have hL₂ : s₂.linearIsometryEquiv (s₁ x - x) = s₁ x - x :=
    linearIsometryEquiv_fixes_orthogonal s₂ η₂ h₂_fix (s₁ x - x)
      (by rw [inner_sub_right]; linarith [inner_affineIsometry_eq s₁ η₂ η₁ h₁_fix horth' x])
  rw [affineIsometryEquiv_add_diff s₁ x (s₂ x) hL₁,
    affineIsometryEquiv_add_diff s₂ x (s₁ x) hL₂]
  abel

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[alcove_closure_compact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma alcove_closure_compact
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {C : W.Alcove}
-- given
  (hess : W.IsEssential)
  (hind : W.IsIndecomposable) :
-- imply
  IsCompact (closure C.set) := by
-- proof
  obtain ⟨n, vertices, hset, _hindep⟩ := alcove_is_simplex W hess hind C
  rw [hset]
  have hfin : Set.Finite (Set.range vertices) := Set.finite_range vertices
  have hcompact : IsCompact (convexHull ℝ (Set.range vertices)) :=
    hfin.isCompact_convexHull ℝ
  have hclosed : IsClosed (convexHull ℝ (Set.range vertices)) :=
    hcompact.isClosed
  apply hcompact.of_isClosed_subset isClosed_closure
  calc closure (interior (convexHull ℝ (Set.range vertices)))
    ⊆ closure (convexHull ℝ (Set.range vertices)) := closure_mono interior_subset
    _ = convexHull ℝ (Set.range vertices) := hclosed.closure_eq

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[arrangement_closure_covers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma arrangement_closure_covers
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {x : E} :
-- imply
  ∃ D : W.Alcove, x ∈ closure D.set := by
-- proof
  have h_carrier_closed : ∀ h : AffineHyperplane E, IsClosed h.carrier :=
    fun h => isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have h_carrier_interior : ∀ h : AffineHyperplane E, interior h.carrier = ∅ := by
    intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hz
    obtain ⟨r, hr_pos, hr_sub⟩ := hz
    have hn_ne : h.normal ≠ 0 := h.normal_ne_zero
    have hn_pos : 0 < ‖h.normal‖ := norm_pos_iff.mpr hn_ne
    set w := z + (r / (2 * ‖h.normal‖)) • h.normal
    have hw_ball : w ∈ Metric.ball z r := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [w, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hr_pos (mul_pos two_pos hn_pos))]
      field_simp; linarith
    have hw_carrier : w ∉ h.carrier := by
      simp only [AffineHyperplane.carrier, Set.mem_setOf_eq, w]
      rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
      have hz_on : ⟪h.normal, z⟫_ℝ = h.offset := by
        have := hr_sub (Metric.mem_ball_self hr_pos)
        simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at this
        exact this
      rw [hz_on]
      intro heq
      have h1 : r / (2 * ‖h.normal‖) > 0 := div_pos hr_pos (mul_pos two_pos hn_pos)
      have h2 : ‖h.normal‖ ^ 2 > 0 := pow_pos hn_pos 2
      linarith [mul_pos h1 h2]
    exact hw_carrier (hr_sub hw_ball)
  obtain ⟨ε, hε_pos, hS_fin⟩ := W.locallyFinite x
  set S := {h ∈ W.arrangement.hyperplanes | (Metric.ball x ε ∩ h.carrier).Nonempty}
  have hS_union_interior : interior (⋃ h ∈ S, h.carrier) = ∅ := by
    classical
    set T := hS_fin.toFinset
    have hST : S = ↑T := (Set.Finite.coe_toFinset hS_fin).symm
    rw [hST]
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.coe_insert, Set.biUnion_insert, Set.eq_empty_iff_forall_notMem]
      intro z hz
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hz
      obtain ⟨r, hr_pos, hr_sub⟩ := hz
      have ha_dense : Dense a.carrierᶜ := by
        rw [← interior_eq_empty_iff_dense_compl]; exact h_carrier_interior a
      have h_rest_dense : Dense (⋃ h ∈ (s : Set (AffineHyperplane E)), h.carrier)ᶜ := by
        rw [← interior_eq_empty_iff_dense_compl]; exact ih
      have hU_open : IsOpen (Metric.ball z r ∩ a.carrierᶜ) :=
        Metric.isOpen_ball.inter (h_carrier_closed a).isOpen_compl
      obtain ⟨p, hp_ball, hp_not_a⟩ := ha_dense.inter_open_nonempty
        (Metric.ball z r) Metric.isOpen_ball ⟨z, Metric.mem_ball_self hr_pos⟩
      obtain ⟨q, ⟨hq_ball, hq_not_a⟩, hq_not_rest⟩ := h_rest_dense.inter_open_nonempty
        (Metric.ball z r ∩ a.carrierᶜ) hU_open ⟨p, hp_ball, hp_not_a⟩
      obtain hcase | hcase := hr_sub hq_ball
      · exact hq_not_a hcase
      · exact hq_not_rest hcase
  have h_find_compl : ∀ r : ℝ, 0 < r → r ≤ ε →
    (Metric.ball x r \ ⋃ h ∈ S, h.carrier).Nonempty := by
    intro r hr_pos _hr_le
    by_contra h_empty
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at h_empty
    have : Metric.ball x r ⊆ interior (⋃ h ∈ S, h.carrier) :=
      Metric.isOpen_ball.subset_interior_iff.mpr h_empty
    have h_ne : (interior (⋃ h ∈ S, h.carrier)).Nonempty :=
      ⟨x, this (Metric.mem_ball_self hr_pos)⟩
    rw [hS_union_interior] at h_ne
    exact Set.not_nonempty_empty h_ne
  have h_in_compl : ∀ y, y ∈ Metric.ball x ε → y ∉ ⋃ h ∈ S, h.carrier →
    y ∈ W.arrangement.complement := by
    intro y hy_ball hy_not_S
    constructor
    · exact Set.mem_univ y
    · intro hy_union
      obtain ⟨h, hh_arr, hy_h⟩ := Set.mem_iUnion₂.mp hy_union
      have hh_S : h ∈ S := ⟨hh_arr, ⟨y, hy_ball, hy_h⟩⟩
      exact hy_not_S (Set.mem_biUnion hh_S hy_h)
  obtain ⟨y₀, hy₀_ball, hy₀_not_S⟩ :=
    h_find_compl (ε / 2) (half_pos hε_pos) (half_le_self (le_of_lt hε_pos))
  have hy₀_in_big_ball : y₀ ∈ Metric.ball x ε :=
    Metric.ball_subset_ball (half_le_self (le_of_lt hε_pos)) hy₀_ball
  have hy₀_compl : y₀ ∈ W.arrangement.complement :=
    h_in_compl y₀ hy₀_in_big_ball hy₀_not_S
  by_cases hxy : x = y₀
  ·
    subst hxy
    set F := W.arrangement.complement
    set CC := connectedComponentIn F x
    have hx_F : x ∈ F := hy₀_compl
    refine ⟨{
      set := CC
      subset_complement := connectedComponentIn_subset F x
      isConnected := isConnected_connectedComponentIn_iff.mpr hx_F
      is_maximal := by
        intro S' hS'_sub hS'_conn hCC_sub
        have hx_S' : x ∈ S' := hCC_sub (mem_connectedComponentIn hx_F)
        exact hS'_conn.isPreconnected.subset_connectedComponentIn hx_S' hS'_sub
    }, ?_⟩
    exact subset_closure (mem_connectedComponentIn hx_F)
  ·
    have hy₀_ne : y₀ - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    have h_crossing_finite : (⋃ h ∈ S,
      if ⟪h.normal, y₀ - x⟫_ℝ = 0 then ∅
      else {(h.offset - ⟪h.normal, x⟫_ℝ) / ⟪h.normal, y₀ - x⟫_ℝ}).Finite := by
      apply Set.Finite.biUnion hS_fin
      intro h _
      split_ifs with hif
      · exact Set.finite_empty
      · exact Set.finite_singleton _
    set crossingTimes := ⋃ h ∈ S,
      if ⟪h.normal, y₀ - x⟫_ℝ = 0 then ∅
      else {(h.offset - ⟪h.normal, x⟫_ℝ) / ⟪h.normal, y₀ - x⟫_ℝ}
    set posCT := crossingTimes ∩ Set.Ioi (0 : ℝ)
    have hposCT_finite : posCT.Finite := h_crossing_finite.subset Set.inter_subset_left
    have h_exists_delta : ∃ δ > 0, δ < 1 ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ h ∈ S, ⟪h.normal, x + t • (y₀ - x)⟫_ℝ ≠ h.offset := by
      have h_crossing_mem : ∀ (t : ℝ) (h : AffineHyperplane E), h ∈ S →
        ⟪h.normal, x + t • (y₀ - x)⟫_ℝ = h.offset → 0 < t → t ∈ posCT := by
        intro t h hh_S heq ht_pos
        constructor
        · simp only [crossingTimes, Set.mem_iUnion₂]
          refine ⟨h, hh_S, ?_⟩
          have h_inner_ne : ⟪h.normal, y₀ - x⟫_ℝ ≠ 0 := by
            intro h_eq_zero
            rw [inner_add_right, inner_smul_right, h_eq_zero, mul_zero, add_zero] at heq
            have hy₀_on : y₀ ∈ h.carrier := by
              simp only [AffineHyperplane.carrier, Set.mem_setOf_eq]
              rw [inner_sub_right] at h_eq_zero
              linarith
            exact hy₀_not_S (Set.mem_biUnion hh_S hy₀_on)
          rw [if_neg h_inner_ne]
          rw [Set.mem_singleton_iff]
          rw [inner_add_right, inner_smul_right] at heq
          field_simp
          linarith
        · exact ht_pos
      by_cases hposCT_empty : posCT = ∅
      · refine ⟨1/2, one_half_pos, one_half_lt_one, ?_⟩
        intro t ht_pos ht_lt h hh_S heq
        have ht_posCT := h_crossing_mem t h hh_S heq ht_pos
        rw [hposCT_empty] at ht_posCT
        exact absurd ht_posCT (Set.notMem_empty _)
      · have hposCT_ne : posCT.Nonempty := Set.nonempty_iff_ne_empty.mpr hposCT_empty
        set m := hposCT_finite.toFinset.min' (by rwa [Set.Finite.toFinset_nonempty])
        have hm_mem : m ∈ posCT := by
          rw [← Set.Finite.mem_toFinset hposCT_finite]
          exact Finset.min'_mem _ _
        have hm_pos : 0 < m := hm_mem.2
        refine ⟨min (m / 2) (1 / 2), lt_min (half_pos hm_pos) one_half_pos,
          lt_of_le_of_lt (min_le_right _ _) one_half_lt_one, ?_⟩
        intro t ht_pos ht_lt h hh_S heq
        have ht_posCT := h_crossing_mem t h hh_S heq ht_pos
        have ht_ge_m : m ≤ t := by
          exact Finset.min'_le _ _ (Set.Finite.mem_toFinset hposCT_finite |>.mpr ht_posCT)
        have : t < m / 2 := lt_of_lt_of_le ht_lt (min_le_left _ _)
        linarith
    obtain ⟨δ, hδ_pos, hδ_lt_one, h_no_cross⟩ := h_exists_delta
    have h_seg_compl : ∀ t : ℝ, 0 < t → t < δ →
      x + t • (y₀ - x) ∈ W.arrangement.complement := by
      intro t ht_pos ht_lt
      constructor
      · exact Set.mem_univ _
      · intro h_union
        obtain ⟨h, hh_arr, hh_mem⟩ := Set.mem_iUnion₂.mp h_union
        simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hh_mem
        have hy₀_dist : dist y₀ x < ε / 2 := by
          exact Metric.mem_ball.mp hy₀_ball
        have h_pt_ball : x + t • (y₀ - x) ∈ Metric.ball x ε := by
          rw [Metric.mem_ball, dist_eq_norm]
          simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
          calc t * ‖y₀ - x‖ < 1 * ‖y₀ - x‖ := by
            apply mul_lt_mul_of_pos_right (lt_trans ht_lt hδ_lt_one)
            exact norm_pos_iff.mpr hy₀_ne
            _ = ‖y₀ - x‖ := one_mul _
            _ = dist y₀ x := (dist_eq_norm y₀ x).symm
            _ < ε / 2 := hy₀_dist
            _ ≤ ε := half_le_self (le_of_lt hε_pos)
        have hh_S : h ∈ S := ⟨hh_arr, ⟨x + t • (y₀ - x), h_pt_ball, by
          simp only [AffineHyperplane.carrier, Set.mem_setOf_eq]; exact hh_mem⟩⟩
        exact h_no_cross t ht_pos ht_lt h hh_S hh_mem
    set seg := (fun t => x + t • (y₀ - x)) '' Set.Ioo 0 δ
    have h_seg_conn : IsConnected seg := by
      apply IsConnected.image
      · exact isConnected_Ioo (by linarith)
      · exact (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
    have h_seg_ne : seg.Nonempty :=
      ⟨x + (δ/2) • (y₀ - x), ⟨δ/2, ⟨half_pos hδ_pos, by linarith⟩, rfl⟩⟩
    have h_seg_sub_compl : seg ⊆ W.arrangement.complement := by
      rintro _ ⟨t, ⟨ht_pos, ht_lt⟩, rfl⟩
      exact h_seg_compl t ht_pos ht_lt
    obtain ⟨z₀, hz₀⟩ := h_seg_ne
    have hz₀_compl : z₀ ∈ W.arrangement.complement := h_seg_sub_compl hz₀
    set F := W.arrangement.complement
    set CC := connectedComponentIn F z₀
    have hz₀_F : z₀ ∈ F := hz₀_compl
    set D : W.Alcove := {
      set := CC
      subset_complement := connectedComponentIn_subset F z₀
      isConnected := isConnected_connectedComponentIn_iff.mpr hz₀_F
      is_maximal := by
        intro S' hS'_sub hS'_conn hCC_sub
        have hz₀_S' : z₀ ∈ S' := hCC_sub (mem_connectedComponentIn hz₀_F)
        exact hS'_conn.isPreconnected.subset_connectedComponentIn hz₀_S' hS'_sub
    }
    refine ⟨D, ?_⟩
    have h_seg_sub_CC : seg ⊆ CC :=
      h_seg_conn.isPreconnected.subset_connectedComponentIn hz₀ h_seg_sub_compl
    rw [mem_closure_iff]
    intro U hU_open hx_U
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU_open x hx_U
    have hy₀_norm_pos : 0 < ‖y₀ - x‖ := norm_pos_iff.mpr hy₀_ne
    set t₀ := min (δ / 2) (r / (2 * ‖y₀ - x‖))
    have ht₀_pos : 0 < t₀ := lt_min (half_pos hδ_pos) (div_pos hr_pos (by positivity))
    have ht₀_lt_δ : t₀ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    set p := x + t₀ • (y₀ - x)
    have hp_seg : p ∈ seg := ⟨t₀, ⟨ht₀_pos, ht₀_lt_δ⟩, rfl⟩
    have hp_CC : p ∈ CC := h_seg_sub_CC hp_seg
    have hp_ball : p ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [p, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht₀_pos]
      calc t₀ * ‖y₀ - x‖
        ≤ r / (2 * ‖y₀ - x‖) * ‖y₀ - x‖ := by
          apply mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
        _ = r / 2 := by field_simp
        _ < r := by linarith
    exact ⟨p, hr_sub hp_ball, hp_CC⟩

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[group_transitive_on_alcoves](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma group_transitive_on_alcoves
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {C D : W.Alcove} :
-- imply
  ∃ w ∈ W.group, ∀ y : E, y ∈ D.set ↔ (w : AffineIsometryEquiv ℝ E E) y ∈ C.set :=
-- proof
W.group_transitive_on_alcoves_aux C D

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[translates_cover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma translates_cover
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {C : W.Alcove}
-- given
  (hess : W.IsEssential)
  (hind : W.IsIndecomposable) :
-- imply
  ∀ x : E, ∃ w ∈ W.group, ((w : AffineIsometryEquiv ℝ E E)⁻¹) x ∈ closure C.set := by
-- proof
  intro x
  obtain ⟨D, hxD⟩ := W.arrangement_closure_covers x
  obtain ⟨w, hw, hmap⟩ := W.group_transitive_on_alcoves C D
  refine ⟨w⁻¹, W.group.inv_mem hw, ?_⟩
  simp only [inv_inv]
  have hDC : (w : AffineIsometryEquiv ℝ E E) '' D.set ⊆ C.set := by
    intro z ⟨y, hyD, hyz⟩
    rw [← hyz]
    exact (hmap y).mp hyD
  have hcont : Continuous (w : AffineIsometryEquiv ℝ E E) := (w : AffineIsometryEquiv ℝ E E).continuous
  exact closure_mono hDC (Set.mem_image_of_mem (w : AffineIsometryEquiv ℝ E E) hxD |>
    (fun h => image_closure_subset_closure_image hcont h))

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[proposition_12_4_discreteness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma proposition_12_4_discreteness
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
-- given
  (hess : W.IsEssential)
  (hind : W.IsIndecomposable) :
-- imply
  ∃ ε > 0, ∀ w ∈ W.TranslationSubgroup, w ≠ 1 → ‖((w : AffineIsometryEquiv ℝ E E) 0 : E)‖ ≥ ε := by
-- proof
  obtain ⟨C⟩ := W.alcove_exists hess hind
  exact W.translation_subgroup_discrete C
    (W.alcove_isOpen hess hind C)
    (W.alcove_nonempty C)
    (W.translation_images_disjoint hess hind C)
    (fun w hw y => W.translation_acts_additively w hw y)
end AffineReflectionGroup


namespace AffineWeylGroup

/--
[origin_hyperplane_in_arrangement](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma origin_hyperplane_in_arrangement
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {Wa : AffineWeylGroup E}
  {η : AffineHyperplane E}
-- given
  (hη : η ∈ Wa.reflGroup.arrangement.hyperplanes) :
-- imply
  ⟨η.normal, 0, η.normal_ne_zero⟩ ∈ Wa.reflGroup.arrangement.hyperplanes := by
-- proof
  rw [Wa.arrangement_eq] at hη ⊢
  simp only [AffineWeylGroupData.affineArrangement, Set.mem_setOf_eq] at hη ⊢
  obtain ⟨α, hα_mem, _, hα_eq, _⟩ := hη
  exact ⟨α, hα_mem, 0, hα_eq, Int.cast_zero.symm⟩

end AffineWeylGroup

namespace AffineWeylGroup

/--
[special_point_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma special_point_exists
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {Wa : AffineWeylGroup E}
-- given
  (hess : Wa.reflGroup.IsEssential)
  (hind : Wa.reflGroup.IsIndecomposable) :
-- imply
  Wa.reflGroup.SpecialPoint (0 : E) := by
-- proof
  intro η hη
  refine ⟨⟨η.normal, 0, η.normal_ne_zero⟩,
    Wa.origin_hyperplane_in_arrangement η hη,
    ⟨1, ?_⟩, ?_⟩
  · exact (one_smul ℝ η.normal).symm
  · simp [AffineHyperplane.carrier, inner_zero_right]
end AffineWeylGroup


namespace AffineWeylGroupData

/--
[AffineHyperplane_ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma AffineHyperplane_ext
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupData E}
-- given
  (h0 h1 : AffineHyperplane E)
  (hn : h0.normal = h1.normal)
  (ho : h0.offset = h1.offset) :
-- imply
  h0 = h1 := by
-- proof
  cases h1; cases h2; simp_all

end AffineWeylGroupData

namespace AffineWeylGroupData

/--
[affineArrangement_locallyFinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma affineArrangement_locallyFinite
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupData E}
-- given
  (hfin : Set.Finite d.roots) :
-- imply
  d.affineArrangement.IsLocallyFinite := by
-- proof
  intro x
  refine ⟨1, one_pos, ?_⟩
  have hS_fin : Set.Finite (⋃ α ∈ d.roots,
    ⋃ k ∈ {k : ℤ | |↑k - ⟪α, x⟫_ℝ| < ‖α‖ + 1},
      ({⟨α, ↑k, d.roots_ne_zero α ‹_›⟩} : Set (AffineHyperplane E))) := by
    apply Set.Finite.biUnion' hfin
    intro α hα
    apply Set.Finite.biUnion
    · apply Set.Finite.subset (Set.finite_Icc
      (⌊⟪α, x⟫_ℝ - (‖α‖ + 1)⌋)
      (⌈⟪α, x⟫_ℝ + (‖α‖ + 1)⌉))
      intro k hk
      simp only [Set.mem_setOf_eq] at hk
      simp only [Set.mem_Icc]
      have hk_abs := abs_sub_lt_iff.mp hk
      exact ⟨Int.floor_le_iff.mpr (by linarith [hk_abs.2]),
        (Int.le_ceil_iff.mpr (by linarith [hk_abs.1]))⟩
    · intro _ _; exact Set.finite_singleton _
  apply hS_fin.subset
  intro η ⟨hη_arr, hη_meet⟩
  obtain ⟨y, hy_ball, hy_carrier⟩ := hη_meet
  obtain ⟨α, hα, k, hα_eq, hk_eq⟩ := hη_arr
  simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hy_carrier
  rw [Metric.mem_ball] at hy_ball
  have h_cs : |⟪α, y - x⟫_ℝ| ≤ ‖α‖ * ‖y - x‖ := abs_real_inner_le_norm α (y - x)
  have h_dist : ‖y - x‖ < 1 := by rwa [← dist_eq_norm]
  have h_bound : |↑k - ⟪α, x⟫_ℝ| < ‖α‖ + 1 := by
    have h1 : ⟪η.normal, y⟫_ℝ = η.offset := hy_carrier
    rw [hα_eq] at h1
    calc |↑k - ⟪α, x⟫_ℝ|
      = |⟪α, y⟫_ℝ - ⟪α, x⟫_ℝ| := by congr 1; linarith [h1, hk_eq]
      _ = |⟪α, y - x⟫_ℝ| := by rw [inner_sub_right]
      _ ≤ ‖α‖ * ‖y - x‖ := h_cs
      _ < ‖α‖ * 1 := by
        obtain h0 | h0 := eq_or_lt_of_le (norm_nonneg α)
        · exfalso
          have : α = 0 := norm_eq_zero.mp h0.symm
          exact d.roots_ne_zero α hα this
        · exact mul_lt_mul_of_pos_left h_dist h0
      _ ≤ ‖α‖ + 1 := by linarith [norm_nonneg α]
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq]
  exact ⟨α, hα, k, h_bound, AffineHyperplane_ext _ _ hα_eq (by linarith [hk_eq])⟩

end AffineWeylGroupData

namespace AffineWeylGroupData

/--
[weylGroup_normalizes_corootLattice](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma weylGroup_normalizes_corootLattice
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupData E} :
-- imply
  ∀ w ∈ d.weylGroup, ∀ v ∈ d.corootLattice, (w : LinearIsometryEquiv (RingHom.id ℝ) E E) v ∈ d.corootLattice :=
-- proof
  d.weylGroup_stable_corootLattice
end AffineWeylGroupData


namespace AffineWeylGroup

/--
[weylGroup_normalizes_corootLattice](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma weylGroup_normalizes_corootLattice
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {Wa : AffineWeylGroup E} :
-- imply
  ∀ w ∈ Wa.data.weylGroup, ∀ v ∈ Wa.data.corootLattice, (w : LinearIsometryEquiv (RingHom.id ℝ) E E) v ∈ Wa.data.corootLattice :=
-- proof
  Wa.data.weylGroup_stable_corootLattice

end AffineWeylGroup


-- created on 2026-10-23
-- updated on 2026-10-24
