import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.Labels
open scoped Classical


variable [DecidableEq V]
/--
[mem_of_getLast?_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Labels.lean)
-/
@[path]
lemma mem_of_getLast?_eq {α : Type*} {l : List α} {a : α}
  (h : l.getLast? = some a) : a ∈ l := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    rw [List.getLast?_cons] at h
    have heq : a = Option.getD xs.getLast? x := (Option.some_injective _ h).symm
    rw [heq]
    cases xs with
    | nil => simp [List.getLast?]
    | cons y ys =>
      simp only [List.getLast?, Option.getD]
      exact List.mem_cons_of_mem x (List.getLast_mem _)

private lemma label_agree_along_chain
  [DecidableEq V]
  {K : SimplicialComplex V}
  [DecidableEq L₁]
  [DecidableEq L₂]
  {lab₁ : Labelling K L₁}
  {lab₂ : Labelling K L₂}
  {f : L₁ → L₂}
  {cs : List (Finset V)}
-- given
  (hadj_prop : ∀ C₁ C₂ : Finset V, K.Adjacent C₁ C₂ → lab₂.labelMap C₁ = (lab₁.labelMap C₁).image f → lab₂.labelMap C₂ = (lab₁.labelMap C₂).image f)
  (hne : cs ≠ [])
  (hchain : List.IsChain K.Adjacent cs)
  (hagree : lab₂.labelMap (cs.head hne) = (lab₁.labelMap (cs.head hne)).image f) :
-- imply
  ∀ D ∈ cs, lab₂.labelMap D = (lab₁.labelMap D).image f := by
-- proof
  induction cs with
  | nil => exact absurd rfl hne
  | cons a tl ih =>
    intro D hD
    rw [List.mem_cons] at hD
    obtain rfl | hD := hD
    · exact hagree
    · cases tl with
      | nil => simp at hD
      | cons b' rest =>
        rw [List.isChain_cons] at hchain
        obtain ⟨hrel, hchain_tl⟩ := hchain
        have hab : K.Adjacent a b' := hrel b' rfl
        have hagree_b : lab₂.labelMap b' = (lab₁.labelMap b').image f :=
          hadj_prop a b' hab hagree
        exact ih (List.cons_ne_nil b' rest) hchain_tl hagree_b D hD

private lemma label_agree_all_chambers
  [DecidableEq V]
  {K : ChamberComplex V}
  [DecidableEq L₁]
  [DecidableEq L₂]
  {lab₁ : Labelling K.toSimplicialComplex L₁}
  {lab₂ : Labelling K.toSimplicialComplex L₂}
  {f : L₁ → L₂}
  {C₀ : Finset V}
-- given
  (hadj_prop : ∀ C₁ C₂ : Finset V, K.toSimplicialComplex.Adjacent C₁ C₂ → lab₂.labelMap C₁ = (lab₁.labelMap C₁).image f → lab₂.labelMap C₂ = (lab₁.labelMap C₂).image f)
  (hC₀ : K.toSimplicialComplex.IsMaximal C₀)
  (hagree₀ : lab₂.labelMap C₀ = (lab₁.labelMap C₀).image f) :
-- imply
  ∀ D, K.toSimplicialComplex.IsMaximal D → lab₂.labelMap D = (lab₁.labelMap D).image f := by
-- proof
  intro D hD
  obtain ⟨gal, hgal_head, hgal_last⟩ := K.gallery_connected C₀ D hC₀ hD
  have hne : gal.chambers ≠ [] := by
    intro h; simp [h] at hgal_head
  have hhead_eq : gal.chambers.head hne = C₀ := by
    rw [List.head?_eq_some_head hne] at hgal_head
    exact Option.some_injective _ hgal_head
  have hD_mem : D ∈ gal.chambers := mem_of_getLast?_eq hgal_last
  exact label_agree_along_chain lab₁ lab₂ f hadj_prop gal.chambers hne
    gal.adjacent_consecutive (hhead_eq ▸ hagree₀) D hD_mem

private lemma label_agree_all_faces
  [DecidableEq V]
  {K : ChamberComplex V}
  [DecidableEq L₁]
  [DecidableEq L₂]
  {lab₁ : Labelling K.toSimplicialComplex L₁}
  {lab₂ : Labelling K.toSimplicialComplex L₂}
  {f : L₁ → L₂}
  {C₀ : Finset V}
-- given
  (hadj_prop : ∀ C₁ C₂ : Finset V, K.toSimplicialComplex.Adjacent C₁ C₂ → lab₂.labelMap C₁ = (lab₁.labelMap C₁).image f → lab₂.labelMap C₂ = (lab₁.labelMap C₂).image f)
  (hsub_prop : ∀ C : Finset V, K.toSimplicialComplex.IsMaximal C → lab₂.labelMap C = (lab₁.labelMap C).image f → ∀ s : Finset V, s ∈ K.toSimplicialComplex.faces → s ⊆ C → lab₂.labelMap s = (lab₁.labelMap s).image f)
  (hC₀ : K.toSimplicialComplex.IsMaximal C₀)
  (hagree₀ : lab₂.labelMap C₀ = (lab₁.labelMap C₀).image f) :
-- imply
  ∀ s ∈ K.toSimplicialComplex.faces, lab₂.labelMap s = (lab₁.labelMap s).image f := by
-- proof
  intro s hs
  obtain ⟨C, hC_max, hsC⟩ := K.exists_maximal s hs
  have hagree_C : lab₂.labelMap C = (lab₁.labelMap C).image f :=
    label_agree_all_chambers lab₁ lab₂ f hadj_prop C₀ hC₀ hagree₀ C hC_max
  exact hsub_prop C hC_max hagree_C s hs hsC

private lemma building_has_chamber
  [DecidableEq V]
  [DecidableEq V]
  {b : Building V} :
-- imply
  ∃ C : Finset V, b.toChamberComplex.toSimplicialComplex.IsMaximal C := by
-- proof
  obtain ⟨A, hA⟩ := b.apartmentSystem.nonempty_apartments
  obtain ⟨s, hs⟩ := b.apartmentSystem.apt_nonempty A hA
  have hs_bldg : s ∈ b.toChamberComplex.toSimplicialComplex.faces :=
    b.apartmentSystem.sub A hA hs
  obtain ⟨C, hC_max, _⟩ := b.toChamberComplex.exists_maximal s hs_bldg
  exact ⟨C, hC_max⟩

private lemma building_label_translation
  [DecidableEq V]
  [DecidableEq V]
  {b : Building V}
  {L₁ : Type}
  {L₂ : Type}
  [DecidableEq L₁]
  [DecidableEq L₂]
  {lab₁ : Labelling b.toChamberComplex.toSimplicialComplex L₁}
  {lab₂ : Labelling b.toChamberComplex.toSimplicialComplex L₂}
  {C₀ : Finset V}
-- given
  (hC₀ : b.toChamberComplex.toSimplicialComplex.IsMaximal C₀) :
-- imply
  ∃ f : L₁ → L₂, Function.Bijective f ∧ lab₂.labelMap C₀ = (lab₁.labelMap C₀).image f := by
-- proof
  obtain ⟨A, hA, hC₀A, _⟩ := b.apartmentSystem.contains_pair C₀ C₀ hC₀ hC₀
  have hC₀_apt_max : A.IsMaximal C₀ :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A hA C₀ hC₀A hC₀
  have hmono₁ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t →
    lab₁.labelMap s ⊂ lab₁.labelMap t := by
    intro s t hs ht hst
    exact lab₁.label_strictMono s t (b.apartmentSystem.sub A hA hs)
      (b.apartmentSystem.sub A hA ht) hst
  have hmono₂ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t →
    lab₂.labelMap s ⊂ lab₂.labelMap t := by
    intro s t hs ht hst
    exact lab₂.label_strictMono s t (b.apartmentSystem.sub A hA hs)
      (b.apartmentSystem.sub A hA ht) hst
  obtain ⟨⟨f, hf_bij, hf_C₀⟩, _⟩ := b.apartmentSystem.apt_unique_labelling A hA
    L₁ L₂ lab₁.labelMap lab₂.labelMap hmono₁ hmono₂ C₀ hC₀_apt_max
  exact ⟨f, hf_bij, hf_C₀⟩

private lemma building_adj_label_propagation
  [DecidableEq V]
  [DecidableEq V]
  {b : Building V}
  {L₁ : Type}
  {L₂ : Type}
  [DecidableEq L₁]
  [DecidableEq L₂]
  {lab₁ : Labelling b.toChamberComplex.toSimplicialComplex L₁}
  {lab₂ : Labelling b.toChamberComplex.toSimplicialComplex L₂}
  {f : L₁ → L₂}
  {C₁ C₂ : Finset V}
-- given
  (hf_bij : Function.Bijective f)
  (hadj : b.toChamberComplex.toSimplicialComplex.Adjacent C₁ C₂)
  (hagree : lab₂.labelMap C₁ = (lab₁.labelMap C₁).image f) :
-- imply
  lab₂.labelMap C₂ = (lab₁.labelMap C₂).image f := by
-- proof
  obtain ⟨hC₁_max, hC₂_max, _, _⟩ := hadj
  obtain ⟨A, hA, hC₁A, hC₂A⟩ := b.apartmentSystem.contains_pair C₁ C₂ hC₁_max hC₂_max
  have hC₁_apt_max : A.IsMaximal C₁ :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A hA C₁ hC₁A hC₁_max
  have hmono₁ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t →
    lab₁.labelMap s ⊂ lab₁.labelMap t := by
    intro s t hs ht hst
    exact lab₁.label_strictMono s t (b.apartmentSystem.sub A hA hs)
      (b.apartmentSystem.sub A hA ht) hst
  have hmono₂ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t →
    lab₂.labelMap s ⊂ lab₂.labelMap t := by
    intro s t hs ht hst
    exact lab₂.label_strictMono s t (b.apartmentSystem.sub A hA hs)
      (b.apartmentSystem.sub A hA ht) hst
  obtain ⟨_, hprop⟩ := b.apartmentSystem.apt_unique_labelling A hA
    L₁ L₂ lab₁.labelMap lab₂.labelMap hmono₁ hmono₂ C₁ hC₁_apt_max
  exact hprop f hf_bij hagree C₂ hC₂A

private lemma building_subface_label_propagation
  [DecidableEq V]
  [DecidableEq V]
  {b : Building V}
  {L₁ : Type}
  {L₂ : Type}
  [DecidableEq L₁]
  [DecidableEq L₂]
  {lab₁ : Labelling b.toChamberComplex.toSimplicialComplex L₁}
  {lab₂ : Labelling b.toChamberComplex.toSimplicialComplex L₂}
  {f : L₁ → L₂}
  {C : Finset V}
  {s : Finset V}
-- given
  (hf_bij : Function.Bijective f)
  (hC : b.toChamberComplex.toSimplicialComplex.IsMaximal C)
  (hagree : lab₂.labelMap C = (lab₁.labelMap C).image f)
  (hs : s ∈ b.toChamberComplex.toSimplicialComplex.faces)
  (hsC : s ⊆ C) :
-- imply
  lab₂.labelMap s = (lab₁.labelMap s).image f := by
-- proof
  obtain ⟨A, hA, hCA, _⟩ := b.apartmentSystem.contains_pair C C hC hC
  have hC_apt_max : A.IsMaximal C :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A hA C hCA hC
  have hs_ne : s.Nonempty :=
    b.toChamberComplex.toSimplicialComplex.nonempty_of_mem s hs
  have hsA : s ∈ A.faces := A.down_closed hCA hsC hs_ne
  have hmono₁ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t →
    lab₁.labelMap s ⊂ lab₁.labelMap t := by
    intro s t hs ht hst
    exact lab₁.label_strictMono s t (b.apartmentSystem.sub A hA hs)
      (b.apartmentSystem.sub A hA ht) hst
  have hmono₂ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t →
    lab₂.labelMap s ⊂ lab₂.labelMap t := by
    intro s t hs ht hst
    exact lab₂.label_strictMono s t (b.apartmentSystem.sub A hA hs)
      (b.apartmentSystem.sub A hA ht) hst
  obtain ⟨_, hprop⟩ := b.apartmentSystem.apt_unique_labelling A hA
    L₁ L₂ lab₁.labelMap lab₂.labelMap hmono₁ hmono₂ C hC_apt_max
  exact hprop f hf_bij hagree s hsA

private lemma mem_of_getLast_eq
  [DecidableEq V]
  {l : List α}
  {a : α}
-- given
  (h : l.getLast? = some a) :
-- imply
  a ∈ l := by
-- proof
  apply mem_of_getLast h


-- created on 2026-10-24
