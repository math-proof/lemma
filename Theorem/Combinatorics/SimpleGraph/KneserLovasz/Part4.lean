/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Def.Combinatorics.SimpleGraph.KneserLovasz.Part5
/-!
# Kneser–Lovász theorem

For `0 < k` and `2 * k ≤ n`, the Kneser graph on the `k`-subsets of an
`n`-element set has chromatic number `n - 2 * k + 2`.
-/


namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

open Finset

theorem knPairing {n : ℕ}
    (L : Finset (Bool × Fin n) → Bool × Fin n) (hanti : knAntipodal L) :
    Even (knTightSet L).card := by
  classical
  have hfT : ∀ σ ∈ knTightSet L, σ.image knNegCell ∈ knTightSet L := by
    intro σ hσ
    rw [knMem_tightSet] at hσ ⊢
    obtain ⟨htight, hnem⟩ := hσ
    have hne : ∀ x ∈ σ, x.Nonempty := by
      intro x hx
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      subst he
      exact hnem hx
    refine ⟨knNegTight σ L hanti htight hne, ?_⟩
    intro hcon
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hcon
    have hx0 : x = ∅ := by
      have hce : x.card = 0 := by
        have hcc := congrArg Finset.card hxe
        rwa [knNegCell_card, Finset.card_empty] at hcc
      exact Finset.card_eq_zero.mp hce
    subst hx0
    exact hnem hx
  have hinv : ∀ σ ∈ knTightSet L,
      (σ.image knNegCell).image knNegCell = σ := by
    intro σ _
    exact knNegImage_invol σ
  have hflip : ∀ σ ∈ knTightSet L,
      (knPosMin σ ↔ ¬ knPosMin (σ.image knNegCell)) := by
    intro σ hσ
    rw [knMem_tightSet] at hσ
    obtain ⟨htight, _⟩ := hσ
    exact knPosMin_flip σ L htight
  have himg_eq : ((knTightSet L).filter knPosMin).image
        (fun σ => σ.image knNegCell) =
      (knTightSet L).filter (fun σ => ¬ knPosMin σ) := by
    ext τ
    constructor
    · intro hm
      obtain ⟨σ, hσ, hστ⟩ := Finset.mem_image.mp hm
      have hσT : σ ∈ knTightSet L := Finset.mem_of_mem_filter _ hσ
      have hP : knPosMin σ := (Finset.mem_filter.mp hσ).2
      have hflipσ := (hflip σ hσT).mp hP
      have hστ' : σ.image knNegCell = τ := hστ
      rw [Finset.mem_filter, ← hστ']
      exact ⟨hfT σ hσT, hflipσ⟩
    · intro hm
      rw [Finset.mem_filter] at hm
      obtain ⟨hτT, hnP⟩ := hm
      have hfτT := hfT τ hτT
      have hP : knPosMin (τ.image knNegCell) := by
        by_contra hcon
        have hback := (hflip τ hτT).mpr hcon
        exact hnP hback
      have hmem1 : τ.image knNegCell ∈ (knTightSet L).filter knPosMin :=
        Finset.mem_filter.mpr ⟨hfτT, hP⟩
      have hinvτ : (τ.image knNegCell).image knNegCell = τ := hinv τ hτT
      exact Finset.mem_image.mpr ⟨τ.image knNegCell, hmem1, hinvτ⟩
  have hinjT1 : Set.InjOn (fun σ => σ.image knNegCell)
      (↑((knTightSet L).filter knPosMin) :
        Set (Finset (Finset (Bool × Fin n)))) := by
    intro a ha b hb hab
    have haT : a ∈ knTightSet L :=
      Finset.mem_of_mem_filter _ (Finset.mem_coe.mp ha)
    have hbT : b ∈ knTightSet L :=
      Finset.mem_of_mem_filter _ (Finset.mem_coe.mp hb)
    have hab' : a.image knNegCell = b.image knNegCell := hab
    have hcon := congrArg (fun σ => σ.image knNegCell) hab'
    rw [hinv a haT, hinv b hbT] at hcon
    exact hcon
  have hcard_img : ((knTightSet L).filter (fun σ => ¬ knPosMin σ)).card =
      ((knTightSet L).filter knPosMin).card := by
    have hci := Finset.card_image_of_injOn hinjT1
    rw [himg_eq] at hci
    exact hci
  have hunion : (knTightSet L).filter knPosMin ∪
      (knTightSet L).filter (fun σ => ¬ knPosMin σ) = knTightSet L := by
    ext σ
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hm, _⟩ | ⟨hm, _⟩)
      · exact hm
      · exact hm
    · intro hm
      by_cases hP : knPosMin σ
      · exact Or.inl ⟨hm, hP⟩
      · exact Or.inr ⟨hm, hP⟩
  have hdisj2 : Disjoint ((knTightSet L).filter knPosMin)
      ((knTightSet L).filter (fun σ => ¬ knPosMin σ)) := by
    rw [Finset.disjoint_left]
    intro σ h1 h2
    rw [Finset.mem_filter] at h1 h2
    exact h2.2 h1.2
  have hsplit : ((knTightSet L).filter knPosMin).card +
      ((knTightSet L).filter (fun σ => ¬ knPosMin σ)).card =
      (knTightSet L).card := by
    have hcu := Finset.card_union_of_disjoint hdisj2
    rw [hunion] at hcu
    omega
  refine ⟨((knTightSet L).filter knPosMin).card, by omega⟩

theorem knTucker {n : ℕ}
    (L : Finset (Bool × Fin n) → Bool × Fin n) (hanti : knAntipodal L) :
    ∃ x y, knConsistent x ∧ knConsistent y ∧ x ⊆ y ∧
      L y = knNegLabel (L x) := by
  classical
  by_contra hcon
  have hnc : knNoCompl L := by
    intro x y hx hy hsub h_eq
    apply hcon
    exact ⟨x, y, hx, hy, hsub, h_eq⟩
  have hodd_eq : Finset.univ.filter (fun σ => Odd ((knG L).degree σ)) =
      insert {∅} (knTightSet L) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    rw [knOddDegree L hnc σ, knMem_tightSet]
  have hnemT : ({∅} : Finset (Finset (Bool × Fin n))) ∉ knTightSet L := by
    rw [knMem_tightSet]
    intro hcon2
    obtain ⟨htight, _⟩ := hcon2
    obtain ⟨_, hcard⟩ := htight
    rw [Finset.card_singleton, knTop_singleton_empty,
      Finset.card_empty] at hcard
    omega
  have hcardS : (Finset.univ.filter (fun σ => Odd ((knG L).degree σ))).card =
      (knTightSet L).card + 1 := by
    rw [hodd_eq, Finset.card_insert_of_notMem hnemT]
  have hevenT := knPairing L hanti
  have hoddS : Odd (Finset.univ.filter
      (fun σ => Odd ((knG L).degree σ))).card := by
    rw [hcardS]
    exact Even.add_one hevenT
  have hevenS : Even (Finset.univ.filter
      (fun σ => Odd ((knG L).degree σ))).card :=
    SimpleGraph.even_card_odd_degree_vertices (knG L)
  exact (Nat.not_even_iff_odd.mpr hoddS) hevenS

theorem knUpper_nonempty {n k : ℕ} (hk : 0 < k) (x : KneserVertex n k) :
    x.val.Nonempty :=
  Finset.card_pos.mp (by rw [x.property]; exact hk)

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted
