import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.ThreeChamber.Part2
open CombinatorialGeometry
open scoped Classical


namespace CombinatorialGeometry

/--
[StrongIsometryImpliesApartment](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/ThreeChamber.lean)
-/
@[path]
lemma StrongIsometryImpliesApartment
  [DecidableEq V]
  {b : Building V}
  {δW : Building.WValuedDist b}
  {Y : Set (Finset V)}
  {A : SimplicialComplex V}
  {φ : Finset V → Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hφ : IsStrongIsometry δW Y (φ '' Y) φ)
  (hφ_img : ∀ C ∈ Y, φ C ∈ A.faces) :
-- imply
  SubsetInApartment b Y := by
-- proof
  obtain ⟨B, hB, hY_in_B⟩ := Building.strong_iso_ext δW hA hφ hφ_img
  exact ⟨B, hB, hY_in_B⟩

end CombinatorialGeometry

namespace CombinatorialGeometry

/--
[identity_strong_isometry_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/ThreeChamber.lean)
-/
@[path]
lemma identity_strong_isometry_of_subset
  [DecidableEq V]
  {b : Building V}
  {δW : Building.WValuedDist b}
  {S : Set (Finset V)}
  {A : SimplicialComplex V}
-- given
  (_hA : A ∈ b.apartmentSystem.apartments)
  (hS : ∀ C ∈ S, C ∈ A.faces)
  (_hS_max : ∀ C ∈ S, b.toSimplicialComplex.IsMaximal C) :
-- imply
  IsStrongIsometry δW S S id ∧ (∀ C ∈ S, id C ∈ A.faces) := by
-- proof
  refine ⟨⟨fun C hC => hC, fun C hC => ⟨C, hC, rfl⟩, fun C hC D hD => rfl⟩,
    fun C hC => hS C hC⟩

end CombinatorialGeometry

namespace CombinatorialGeometry

/--
[threeChamberHypotheses_of_building](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/ThreeChamber.lean)
-/
@[path]
lemma threeChamberHypotheses_of_building
  [DecidableEq V]
  {b : Building V} :
-- imply
  ThreeChamberHypotheses b where gallery_concat := by
-- proof
  intro C₁ C₂ C₃ g₁ g₂ hconn₁ hconn₂
  have hne₁ : g₁.chambers ≠ [] := List.ne_nil_of_length_pos g₁.length_pos
  have hne₂ : g₂.chambers ≠ [] := List.ne_nil_of_length_pos g₂.length_pos
  have hhead₂ : g₂.chambers.head? = some C₂ := hconn₂.1
  have hlast₁ : g₁.chambers.getLast? = some C₂ := hconn₁.2
  have hlast₂ : g₂.chambers.getLast? = some C₃ := hconn₂.2
  have ⟨rest₂, hg₂_eq⟩ : ∃ rest₂, g₂.chambers = C₂ :: rest₂ := by
    obtain ⟨a, t, heq⟩ := List.exists_cons_of_ne_nil hne₂
    rw [heq, List.head?] at hhead₂
    simp at hhead₂
    exact ⟨t, by rw [heq, hhead₂]⟩
  set cs := g₁.chambers ++ rest₂ with cs_def
  have hcs_pos : cs.length > 0 := by
    rw [cs_def, List.length_append]
    have := g₁.length_pos
    omega
  have hcs_max : ∀ C ∈ cs, b.toSimplicialComplex.IsMaximal C := by
    intro C hC
    rw [cs_def, List.mem_append] at hC
    obtain h | h := hC
    · exact g₁.all_maximal C h
    · exact g₂.all_maximal C (hg₂_eq ▸ List.mem_cons_of_mem _ h)
  have hcs_chain : List.IsChain b.toSimplicialComplex.Adjacent cs := by
    rw [cs_def, List.isChain_append]
    refine ⟨g₁.adjacent_consecutive, (hg₂_eq ▸ g₂.adjacent_consecutive).tail, ?_⟩
    intro x hx y hy
    rw [Option.mem_def] at hx hy
    have hx_eq : x = C₂ := by
      have : g₁.chambers.getLast? = some x := hx
      rw [hlast₁] at this
      exact (Option.some_injective _ this).symm
    subst hx_eq
    cases rest₂ with
    | nil => simp [List.head?] at hy
    | cons a t =>
      simp [List.head?] at hy
      subst hy
      exact (hg₂_eq ▸ g₂.adjacent_consecutive).rel_head
  refine ⟨⟨cs, hcs_pos, hcs_max, hcs_chain⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  ·
    show cs.head? = some C₁
    rwa [cs_def, List.head?_append_of_ne_nil _ hne₁]
  ·
    show cs.getLast? = some C₃
    rw [cs_def, List.getLast?_append]
    cases rest₂ with
    | nil =>
      simp [Option.or, List.getLast?]
      rw [hg₂_eq] at hlast₂
      simp [List.getLast?] at hlast₂
      rwa [← hlast₂]
    | cons a t =>
      have hne_rest : (a :: t) ≠ [] := List.cons_ne_nil _ _
      have hsome := List.getLast?_eq_some_getLast hne_rest
      rw [hsome, Option.some_or]
      rw [hg₂_eq] at hlast₂
      rw [List.getLast?_cons_cons] at hlast₂
      rwa [← hsome]
  ·
    show cs.length - 1 = g₁.length + g₂.length
    rw [cs_def, List.length_append]
    simp only [Gallery.length]
    have hg₂_len : g₂.chambers.length = rest₂.length + 1 := by
      rw [hg₂_eq, List.length_cons]
    have := g₁.length_pos
    omega
  ·
    show C₂ ∈ cs
    rw [cs_def, List.mem_append]
    left
    exact List.mem_of_getLast? hlast₁
  minimal_gallery_exists := by
    intro C D hC hD
    by_cases h : C = D
    ·
      subst h
      exact ⟨⟨[C], by simp, fun E hE => by simp at hE; subst hE; exact hC,
        List.IsChain.singleton C⟩,
        ⟨by simp, by simp⟩,
        by simp [Gallery.length, galleryDist_self]⟩
    ·
      obtain ⟨g₀, hconn₀⟩ := b.toChamberComplex.gallery_connected C D hC hD
      have hne : {n | ∃ g : Gallery b.toSimplicialComplex, g.Connects C D ∧ g.length = n}.Nonempty :=
        ⟨g₀.length, g₀, ⟨hconn₀.1, hconn₀.2⟩, rfl⟩
      obtain ⟨g, hconn, hlen⟩ := Nat.sInf_mem hne
      exact ⟨g, hconn, by unfold galleryDist; rw [if_neg h]; exact hlen⟩

end CombinatorialGeometry

namespace CombinatorialGeometry

/--
[three_chambers_common_apartment](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/ThreeChamber.lean)
-/
@[path]
lemma three_chambers_common_apartment
  [DecidableEq V]
  {b : Building V}
  {C₁ C₂ C₃ : Finset V}
-- given
  (hyp : ThreeChamberHypotheses b)
  (hC₁ : b.toSimplicialComplex.IsMaximal C₁)
  (hC₂ : b.toSimplicialComplex.IsMaximal C₂)
  (hC₃ : b.toSimplicialComplex.IsMaximal C₃)
  (hcollinear : galleryDist b.toSimplicialComplex C₁ C₃ = galleryDist b.toSimplicialComplex C₁ C₂ + galleryDist b.toSimplicialComplex C₂ C₃) :
-- imply
  ∃ A ∈ b.apartmentSystem.apartments, C₁ ∈ A.faces ∧ C₂ ∈ A.faces ∧ C₃ ∈ A.faces := by
-- proof
  obtain ⟨g₁, hconn₁, hmin₁⟩ := hyp.minimal_gallery_exists C₁ C₂ hC₁ hC₂
  obtain ⟨g₂, hconn₂, hmin₂⟩ := hyp.minimal_gallery_exists C₂ C₃ hC₂ hC₃
  obtain ⟨g₃, hconn₃, hlen₃, hC₂_mem⟩ :=
    hyp.gallery_concat C₁ C₂ C₃ g₁ g₂ hconn₁ hconn₂
  have hmin₃ : g₃.length = galleryDist b.toSimplicialComplex C₁ C₃ := by
    rw [hlen₃, hmin₁, hmin₂, ← hcollinear]
  obtain ⟨A, hA, hC₁A, hC₃A⟩ := b.apartmentSystem.contains_pair C₁ C₃ hC₁ hC₃
  have hall_in_A : ∀ E ∈ g₃.chambers, E ∈ A.faces :=
    b.apartmentSystem.gallery_convex A hA C₁ C₃ hC₁A hC₁ hC₃A hC₃ g₃ hconn₃ hmin₃
  exact ⟨A, hA, hC₁A, hall_in_A C₂ hC₂_mem, hC₃A⟩

end CombinatorialGeometry


-- created on 2026-10-23
