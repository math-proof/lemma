import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2


/--
[canonical_retraction_onto_apartment](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Basic.lean)
-/
@[path]
lemma canonical_retraction_onto_apartment
  [DecidableEq V]
  [DecidableEq V]
  {K : ChamberComplex V}
  {𝒜 : ApartmentSystem K}
  {B : SimplicialComplex V}
  {C₀ : Finset V}
-- given
  (hB : B ∈ 𝒜.apartments)
  (hC₀_B : C₀ ∈ B.faces)
  (hC₀_max_B : B.IsMaximal C₀) :
-- imply
  ∃ ρ : Finset V → Finset V, (∀ D, K.toSimplicialComplex.IsMaximal D → ρ D ∈ B.faces) ∧ (∀ D, B.IsMaximal D → ρ D = D) := by
-- proof
  classical
  have hC₀_K_max : K.toSimplicialComplex.IsMaximal C₀ :=
    𝒜.maximal_in_apt_is_maximal B hB C₀ hC₀_max_B
  have retract_img : ∀ D, K.toSimplicialComplex.IsMaximal D →
    ∃ E, E ∈ B.faces := by
    intro D hD_max
    obtain ⟨A', hA'mem, hC₀_in_A', hD_in_A'⟩ := 𝒜.contains_pair C₀ D hC₀_K_max hD_max
    have hC₀_max_A' := 𝒜.building_maximal_in_apt_is_apt_maximal A' hA'mem C₀
      hC₀_in_A' hC₀_K_max
    obtain ⟨φ, _, _⟩ := 𝒜.iso_exists A' hA'mem B hB C₀ hC₀_in_A' hC₀_B
      C₀ hC₀_max_A' hC₀_B
    exact ⟨D.image φ.toFun, φ.map_face D hD_in_A'⟩
  refine ⟨fun D => if B.IsMaximal D then D
    else if h : K.toSimplicialComplex.IsMaximal D then (retract_img D h).choose
    else D, fun D hD_max => ?_, fun D hD_Bmax => ?_⟩
  ·
    dsimp only
    split_ifs with hBmax
    · exact hBmax.1
    · exact (retract_img D hD_max).choose_spec
  ·
    dsimp only
    split_ifs
    rfl

private lemma list_boundary_crossing
  [DecidableEq V]
  {R : α → α → Prop}
  {l : List α}
  [DecidablePred P]
-- given
  (P : α → Prop)
  (hl : l ≠ [])
  (hchain : List.IsChain R l)
  (hhead : P (l.head hl))
  (hlast : ¬P (l.getLast hl)) :
-- imply
  ∃ a b, a ∈ l ∧ b ∈ l ∧ P a ∧ ¬P b ∧ R a b := by
-- proof
  induction l with
  | nil => exact absurd rfl hl
  | cons x xs ih =>
    by_cases hxs : xs = []
    · subst hxs; simp at hhead hlast; exact absurd hhead hlast
    · by_cases hP_next : P (xs.head hxs)
      · have hchain_rest := hchain.tail
        have hlast_xs : ¬P (xs.getLast hxs) := by rwa [List.getLast_cons hxs] at hlast
        obtain ⟨a, b, ha, hb, hPa, hnPb, hRab⟩ :=
          ih hxs hchain_rest hP_next hlast_xs
        exact ⟨a, b, List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb, hPa, hnPb, hRab⟩
      · have heq : xs = xs.head hxs :: xs.tail := (List.cons_head_tail hxs).symm
        rw [heq] at hchain
        exact ⟨x, xs.head hxs, List.mem_cons_self, List.mem_cons_of_mem _ (List.head_mem hxs),
          by simpa using hhead, hP_next, List.IsChain.rel hchain⟩

private lemma ApartmentSystem.apt_gallery_boundary
  [DecidableEq V]
  [DecidableEq V]
  {K : ChamberComplex V}
  {𝒜 : ApartmentSystem K}
  {A : SimplicialComplex V}
  {Y₀ : Set (Finset V)}
-- given
  (hA : A ∈ 𝒜.apartments)
  (hY₀_sub : ∀ C ∈ Y₀, A.IsMaximal C)
  (hY₀_nonempty : Y₀.Nonempty)
  (hY₀_proper : ∃ D, A.IsMaximal D ∧ D ∉ Y₀) :
-- imply
  ∃ C', A.IsMaximal C' ∧ C' ∉ Y₀ ∧ ∃ D ∈ Y₀, A.Adjacent C' D := by
-- proof
  classical
  obtain ⟨B_idx, M, cc, hcc_eq, _φ, _hinj, _hsurj, _hadj, _hthin⟩ :=
    𝒜.apt_is_coxeter A hA
  subst hcc_eq
  obtain ⟨C_in, hC_in⟩ := hY₀_nonempty
  obtain ⟨D_out, hD_out_max, hD_out_not⟩ := hY₀_proper
  have hC_in_max := hY₀_sub C_in hC_in
  have hD_out_max' := hD_out_max
  obtain ⟨g, hg_head, hg_last⟩ := cc.gallery_connected C_in D_out hC_in_max hD_out_max'
  have hg_ne : g.chambers ≠ [] := List.ne_nil_of_length_pos g.length_pos
  have hg_head_val : g.chambers.head hg_ne = C_in := by
    have h := List.head?_eq_some_head hg_ne; rw [h] at hg_head
    exact Option.some_injective _ hg_head
  have hg_last_val : g.chambers.getLast hg_ne = D_out := by
    have h := List.getLast?_eq_some_getLast hg_ne; rw [h] at hg_last
    exact Option.some_injective _ hg_last
  have hchain := g.adjacent_consecutive
  have hhead_P : (g.chambers.head hg_ne) ∈ Y₀ := hg_head_val ▸ hC_in
  have hlast_nP : (g.chambers.getLast hg_ne) ∉ Y₀ := hg_last_val ▸ hD_out_not
  obtain ⟨a, b, _ha_mem, _hb_mem, ha_in, hb_not, hab_adj⟩ :=
    list_boundary_crossing g.chambers (· ∈ Y₀) hg_ne hchain hhead_P hlast_nP
  have hb_max : cc.toSimplicialComplex.IsMaximal b := hab_adj.2.1
  exact ⟨b, hb_max, hb_not, a, ha_in, cc.toSimplicialComplex.adjacent_symm _ _ hab_adj⟩

private lemma nonmaximal_galleryDist_zero
  [DecidableEq V]
  {K : SimplicialComplex V}
  {C : Finset V}
  {D : Finset V}
-- given
  (hnomax : ¬ K.IsMaximal C) :
-- imply
  galleryDist K C D = 0 := by
-- proof
  by_cases hCD : C = D
  · subst hCD; exact galleryDist_self K C
  · unfold galleryDist
    simp only [hCD, ↓reduceIte]
    have hempty : {n | ∃ g : Gallery K, g.Connects C D ∧ g.length = n} = ∅ := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨g, hconn, -⟩
      apply hnomax
      have hne_nil : g.chambers ≠ [] := by
        intro h
        have := g.length_pos
        simp [h] at this
      have hhead := hconn.1
      rw [List.head?_eq_some_head hne_nil] at hhead
      have heq := Option.some_injective _ hhead
      rw [← heq]
      exact g.all_maximal _ (List.head_mem hne_nil)
    rwa [hempty]

private lemma galleryDist_pos_of_maximal_ne
  [DecidableEq V]
  {K : ChamberComplex V}
  {C D : Finset V}
-- given
  (hCmax : K.toSimplicialComplex.IsMaximal C)
  (hDmax : K.toSimplicialComplex.IsMaximal D)
  (hne : C ≠ D) :
-- imply
  0 < galleryDist K.toSimplicialComplex C D := by
-- proof
  unfold galleryDist
  simp only [hne, ↓reduceIte]
  obtain ⟨g, hg_head, hg_last⟩ := K.gallery_connected C D hCmax hDmax
  have hnonempty : {n | ∃ g : Gallery K.toSimplicialComplex,
    g.Connects C D ∧ g.length = n}.Nonempty :=
    ⟨g.length, g, ⟨hg_head, hg_last⟩, rfl⟩
  by_contra h
  push Not at h
  have h0 : sInf {n | ∃ g : Gallery K.toSimplicialComplex,
    g.Connects C D ∧ g.length = n} = 0 := Nat.le_zero.mp h
  rw [Nat.sInf_eq_zero] at h0
  obtain ⟨g0, ⟨hconn0_head, hconn0_last⟩, hlen0⟩ | hempty := h0
  ·
    have hcl : g0.chambers.length = 1 := by
      have := g0.length_pos; unfold Gallery.length at hlen0; omega
    have hone : ∃ x, g0.chambers = [x] := by
      match g0.chambers, hcl with
      | [x], _ => exact ⟨x, rfl⟩
    obtain ⟨x, hx⟩ := hone
    simp [hx] at hconn0_head hconn0_last
    exact hne (hconn0_head.symm.trans hconn0_last)
  · exact absurd hempty (Set.nonempty_iff_ne_empty.mp hnonempty)


-- created on 2026-10-24
