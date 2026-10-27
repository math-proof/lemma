import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.Convexity
open scoped Classical


/--
[chain_exists_transition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Convexity.lean)
-/
@[path]
lemma chain_exists_transition
  [DecidableEq V]
  {R : α → α → Prop}
  {a b : α}
  {l : List α}
  {E : α}
-- given
  (hchain : List.IsChain R (a :: b :: l))
  (P : α → Prop)
  (hPa : P a)
  (hE_mem : E ∈ a :: b :: l)
  (hE_not : ¬ P E) :
-- imply
  ∃ x y, x ∈ a :: b :: l ∧ y ∈ a :: b :: l ∧ R x y ∧ P x ∧ ¬ P y := by
-- proof
  by_cases hPb : P b
  · have hchain_tail : List.IsChain R (b :: l) := hchain.tail
    have hE_tail : E ∈ b :: l := by
      cases hE_mem with
      | head => exact absurd hPa hE_not
      | tail _ h => exact h
    cases l with
    | nil =>
      simp at hE_tail
      subst hE_tail
      exact absurd hPb hE_not
    | cons c l' =>
      obtain ⟨x, y, hx, hy, hR, hPx, hnPy⟩ :=
        chain_exists_transition hchain_tail P hPb E hE_tail hE_not
      exact ⟨x, y, List.mem_cons_of_mem a hx, List.mem_cons_of_mem a hy,
        hR, hPx, hnPy⟩
  · exact ⟨a, b, .head _, .tail _ (.head _), hchain.rel_head, hPa, hPb⟩

/--
[maximal_in_building_and_subcomplex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Convexity.lean)
-/
@[path]
lemma maximal_in_building_and_subcomplex
  [DecidableEq V]
  {K A : SimplicialComplex V}
  {C : Finset V}
-- given
  (hAK : IsSubcomplex A K)
  (hC_A : C ∈ A.faces)
  (hC_K_max : K.IsMaximal C) :
-- imply
  A.IsMaximal C :=
-- proof
  ⟨hC_A, fun y hy hsub => hC_K_max.2 y (hAK hy) hsub⟩

/--
[finset_image_eq_self_of_fixes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Convexity.lean)
-/
@[path]
lemma finset_image_eq_self_of_fixes
  [DecidableEq V]
  {f : V → V}
  {s : Finset V}
-- given
  (hfix : ∀ v ∈ s, f v = v) :
-- imply
  s.image f = s := by
-- proof
  ext v
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩; rwa [hfix w hw]
  · intro hv; exact ⟨v, hv, hfix v hv⟩

/--
[Building.ApartmentsAreConvex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Convexity.lean)
-/
@[path]
lemma Building.ApartmentsAreConvex
  [DecidableEq V]
  {b : Building V} :
-- imply
  ∀ A ∈ b.apartmentSystem.apartments, ∀ C D : Finset V, C ∈ A.faces → A.IsMaximal C → D ∈ A.faces → A.IsMaximal D → ∀ g : Gallery b.toSimplicialComplex, g.Connects C D → g.length = galleryDist b.toSimplicialComplex C D → ∀ E ∈ g.chambers, E ∈ A.faces := by
-- proof
  intro A hA C D hC hCmax hD hDmax g hconn hmin E hEmem
  exact b.apartmentSystem.gallery_convex A hA C D hC
    (b.apartmentSystem.maximal_in_apt_is_maximal A hA C hCmax)
    hD (b.apartmentSystem.maximal_in_apt_is_maximal A hA D hDmax)
    g hconn hmin E hEmem


-- created on 2026-10-23
