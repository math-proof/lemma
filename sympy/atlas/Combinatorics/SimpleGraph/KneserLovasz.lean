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

/-!
# Kneser–Lovász theorem

For `0 < k` and `2 * k ≤ n`, the Kneser graph on the `k`-subsets of an
`n`-element set has chromatic number `n - 2 * k + 2`.
-/

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

open Finset

abbrev KneserVertex (n k : ℕ) := { s : Finset (Fin n) // s.card = k }

def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj x y := Disjoint x.val y.val ∧ x ≠ y
  symm.symm := by
    intro a b ⟨hdisj, hne⟩
    exact ⟨hdisj.symm, hne.symm⟩
  loopless.irrefl := by
    intro a ⟨_, hne⟩
    exact hne rfl

instance (n k : ℕ) : DecidableRel (kneserGraph n k).Adj := by
  unfold kneserGraph
  infer_instance

private def knNegLabel {n : ℕ} (l : Bool × Fin n) : Bool × Fin n := (!l.1, l.2)

private theorem knNegLabel_inj {n : ℕ} : Function.Injective (@knNegLabel n) :=
  knNegLabel_invol.injective

private def knNegLabelEmb {n : ℕ} : (Bool × Fin n) ↪ (Bool × Fin n) :=
  ⟨knNegLabel, knNegLabel_inj⟩

private def knNegCell {n : ℕ} (x : Finset (Bool × Fin n)) : Finset (Bool × Fin n) :=
  x.map knNegLabelEmb

private def knConsistent {n : ℕ} (x : Finset (Bool × Fin n)) : Prop :=
  ∀ l ∈ x, knNegLabel l ∉ x

private def knIsChain {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) : Prop :=
  ∀ a ∈ σ, ∀ b ∈ σ, a ⊆ b ∨ b ⊆ a

private def knChain {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) : Prop :=
  σ.Nonempty ∧ (∀ x ∈ σ, knConsistent x) ∧ knIsChain σ

private def knTop {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) :
    Finset (Bool × Fin n) :=
  σ.sup id

private def knImg {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Finset (Bool × Fin n) :=
  σ.image L

private def knHappy {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Prop :=
  knChain σ ∧ knTop σ ⊆ knImg σ L

private def knTight {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Prop :=
  knHappy σ L ∧ σ.card = (knTop σ).card

private def knLoose {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Prop :=
  knHappy σ L ∧ σ.card = (knTop σ).card + 1

private def knAntipodal {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n) : Prop :=
  ∀ x, knConsistent x → x.Nonempty → L (knNegCell x) = knNegLabel (L x)

private def knNoCompl {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n) : Prop :=
  ∀ x y, knConsistent x → knConsistent y → x ⊆ y → L y ≠ knNegLabel (L x)

open Classical in
private noncomputable def knOut {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Finset (Finset (Bool × Fin n)) :=
  Finset.univ.filter (fun v => v ∉ σ ∧ knChain (insert v σ) ∧ knTop (insert v σ) ⊆ knImg σ L)

open Classical in
private noncomputable def knIn {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Finset (Finset (Bool × Fin n)) :=
  σ.filter (fun w => knHappy (σ.erase w) L ∧ knTop σ ⊆ knImg (σ.erase w) L)

private def knGAdj {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n)
    (σ τ : Finset (Finset (Bool × Fin n))) : Prop :=
  knHappy σ L ∧ knHappy τ L ∧
    ((∃ v, v ∉ σ ∧ τ = insert v σ ∧ knTop τ ⊆ knImg σ L) ∨
     (∃ w, w ∉ τ ∧ σ = insert w τ ∧ knTop σ ⊆ knImg τ L))

private theorem knGAdj_symm {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n)
    (σ τ : Finset (Finset (Bool × Fin n))) (h : knGAdj L σ τ) : knGAdj L τ σ := by
  classical
  obtain ⟨hs, ht, hdoor⟩ := h
  exact ⟨ht, hs, hdoor.elim Or.inr Or.inl⟩

private theorem knGAdj_irrefl {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n)
    (σ : Finset (Finset (Bool × Fin n))) (h : knGAdj L σ σ) : False := by
  classical
  obtain ⟨_, _, hdoor⟩ := h
  rcases hdoor with ⟨v, hv, heq, _⟩ | ⟨w, hw, heq, _⟩
  · have hcc := congrArg Finset.card heq
    rw [Finset.card_insert_of_notMem hv] at hcc
    omega
  · have hcc := congrArg Finset.card heq
    rw [Finset.card_insert_of_notMem hw] at hcc
    omega

private def knG {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n) :
    SimpleGraph (Finset (Finset (Bool × Fin n))) where
  Adj := knGAdj L
  symm := ⟨fun σ τ h => knGAdj_symm L σ τ h⟩
  loopless := ⟨fun σ h => knGAdj_irrefl L σ h⟩

private noncomputable instance knGDec {n : ℕ}
    (L : Finset (Bool × Fin n) → Bool × Fin n) :
    DecidableRel (knG L).Adj :=
  Classical.decRel _

private theorem knNegCell_consistent {n : ℕ} {x : Finset (Bool × Fin n)}
    (hcons : knConsistent x) : knConsistent (knNegCell x) := by
  classical
  intro l hl hnl
  obtain ⟨m, hm, hml⟩ := knMem_negCell.mp hl
  obtain ⟨m', hm', hm'l⟩ := knMem_negCell.mp hnl
  have hme : m' = l := knNegLabel_inj hm'l
  have hmem : knNegLabel m ∈ x := by
    rw [hml]
    rw [hme] at hm'
    exact hm'
  exact hcons m hm hmem

private theorem knNegChain {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (h : knChain σ) : knChain (σ.image knNegCell) := by
  classical
  obtain ⟨hne, hcons, hisch⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨knNegCell x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    rw [← hxy]
    exact knNegCell_consistent (hcons x hx)
  · intro a ha b hb
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp ha
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hb
    rcases hisch x hx z hz with hsub | hsub
    · left
      rw [← hxy, ← hzy]
      exact knNegCell_mono hsub
    · right
      rw [← hxy, ← hzy]
      exact knNegCell_mono hsub

private theorem knNegTight {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (hanti : knAntipodal L)
    (h : knTight σ L) (hne : ∀ x ∈ σ, x.Nonempty) :
    knTight (σ.image knNegCell) L := by
  classical
  obtain ⟨⟨hchain, hsub⟩, hcard⟩ := h
  have hchainI := knNegChain σ hchain
  have htopI : knTop (σ.image knNegCell) = knNegCell (knTop σ) :=
    knNegTop σ hchain
  have himgI : knImg (σ.image knNegCell) L = knNegCell (knImg σ L) := by
    ext ℓ
    constructor
    · intro hm
      obtain ⟨y, hy, hyl⟩ := Finset.mem_image.mp hm
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      have hxL : L (knNegCell x) = knNegLabel (L x) :=
        hanti x (hchain.2.1 x hx) (hne x hx)
      rw [← hxy] at hyl
      rw [hxL] at hyl
      have hmem : knNegLabel (L x) ∈ knNegCell (knImg σ L) :=
        knNegLabel_mem_negCell (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      rwa [hyl] at hmem
    · intro hm
      obtain ⟨m, hm2, hml⟩ := knMem_negCell.mp hm
      obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hm2
      have hxL : L (knNegCell x) = knNegLabel (L x) :=
        hanti x (hchain.2.1 x hx) (hne x hx)
      have hmemI : knNegCell x ∈ σ.image knNegCell :=
        Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have hmemL : L (knNegCell x) ∈ knImg (σ.image knNegCell) L :=
        Finset.mem_image.mpr ⟨knNegCell x, hmemI, rfl⟩
      rw [hxL, hxm, hml] at hmemL
      exact hmemL
  refine ⟨⟨hchainI, ?_⟩, ?_⟩
  · rw [htopI, himgI]
    exact knNegCell_mono hsub
  · rw [htopI, knNegCell_card,
      Finset.card_image_of_injective σ knNegCell_injective]
    exact hcard

private def knPosMin {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) : Prop :=
  ∃ i, (true, i) ∈ knTop σ ∧ ∀ j ∈ (knTop σ).image Prod.snd, i ≤ j

open Classical in
private noncomputable def knTightSet {n : ℕ}
    (L : Finset (Bool × Fin n) → Bool × Fin n) :
    Finset (Finset (Finset (Bool × Fin n))) :=
  Finset.univ.filter (fun σ => knTight σ L ∧ ∅ ∉ σ)

private theorem knPairing {n : ℕ}
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

private theorem knTucker {n : ℕ}
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

private theorem knUpper_nonempty {n k : ℕ} (hk : 0 < k) (x : KneserVertex n k) :
    x.val.Nonempty :=
  Finset.card_pos.mp (by rw [x.property]; exact hk)

private def knUpperColorFn {n k : ℕ} (hk : 0 < k) (x : KneserVertex n k) :
    Fin (n - 2 * k + 1 + 1) :=
  ⟨min (x.val.min' (knUpper_nonempty hk x)).val (n - 2 * k + 1), by omega⟩

private theorem knUpperColoring {n k : ℕ} (hk : 0 < k) (h : 2 * k ≤ n) :
    (kneserGraph n k).Colorable (n - 2 * k + 1 + 1) := by
  classical
  refine ⟨SimpleGraph.Coloring.mk (knUpperColorFn hk) ?_⟩
  intro v w hadj
  obtain ⟨hdisj, _⟩ := hadj
  intro heq
  have hnev' : v.val.Nonempty := knUpper_nonempty hk v
  have hnew' : w.val.Nonempty := knUpper_nonempty hk w
  have e1 : (knUpperColorFn hk v).val =
      min (v.val.min' hnev').val (n - 2 * k + 1) := rfl
  have e2 : (knUpperColorFn hk w).val =
      min (w.val.min' hnew').val (n - 2 * k + 1) := rfl
  have hval : min (v.val.min' hnev').val (n - 2 * k + 1) =
      min (w.val.min' hnew').val (n - 2 * k + 1) := by
    rw [← e1, ← e2]
    exact congrArg Fin.val heq
  have hmv : v.val.min' hnev' ∈ v.val := Finset.min'_mem _ _
  have hmw : w.val.min' hnew' ∈ w.val := Finset.min'_mem _ _
  have hleV : ∀ a ∈ v.val, v.val.min' hnev' ≤ a :=
    fun a ha => (v.val.isLeast_min' hnev').2 (Finset.mem_coe.mpr ha)
  have hleW : ∀ a ∈ w.val, w.val.min' hnew' ≤ a :=
    fun a ha => (w.val.isLeast_min' hnew').2 (Finset.mem_coe.mpr ha)
  by_cases hlt : (knUpperColorFn hk v).val < n - 2 * k + 1
  · rw [e1] at hlt
    have hcN : (v.val.min' hnev').val < n - 2 * k + 1 := by omega
    have hav : (v.val.min' hnev').val = (knUpperColorFn hk v).val := by
      rw [e1]
      exact (Nat.min_eq_left (le_of_lt hcN)).symm
    have hcbN : (w.val.min' hnew').val < n - 2 * k + 1 := by omega
    have hbw : (w.val.min' hnew').val = (knUpperColorFn hk v).val := by
      have hminw : min (w.val.min' hnew').val (n - 2 * k + 1) =
          (knUpperColorFn hk v).val := by
        rw [← hval]
        exact e1.symm
      rw [← hminw]
      exact (Nat.min_eq_left (le_of_lt hcbN)).symm
    have hcn : (knUpperColorFn hk v).val < n := by omega
    have hzv : v.val.min' hnev' = ⟨(knUpperColorFn hk v).val, hcn⟩ :=
      Fin.ext hav
    have hzw : w.val.min' hnew' = ⟨(knUpperColorFn hk v).val, hcn⟩ :=
      Fin.ext hbw
    have hmem1 : (⟨(knUpperColorFn hk v).val, hcn⟩ : Fin n) ∈ v.val := hzv ▸ hmv
    have hmem2 : (⟨(knUpperColorFn hk v).val, hcn⟩ : Fin n) ∈ w.val := hzw ▸ hmw
    exact (Finset.disjoint_left.mp hdisj) hmem1 hmem2
  · have hNle : n - 2 * k + 1 ≤ (knUpperColorFn hk v).val :=
      le_of_not_gt hlt
    have hgeV : ∀ a ∈ v.val, n - 2 * k + 1 ≤ a.val := by
      intro a ha
      have h1 : v.val.min' hnev' ≤ a := hleV a ha
      have h2 : (v.val.min' hnev').val ≤ a.val := by exact_mod_cast h1
      have h3 : n - 2 * k + 1 ≤ (v.val.min' hnev').val := by omega
      omega
    have hgeW : ∀ a ∈ w.val, n - 2 * k + 1 ≤ a.val := by
      intro a ha
      have h1 : w.val.min' hnew' ≤ a := hleW a ha
      have h2 : (w.val.min' hnew').val ≤ a.val := by exact_mod_cast h1
      have h3 : n - 2 * k + 1 ≤ (w.val.min' hnew').val := by omega
      omega
    have hsubV : v.val ⊆
        Finset.univ.filter (fun a : Fin n => n - 2 * k + 1 ≤ a.val) := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hgeV a ha⟩
    have hsubW : w.val ⊆
        Finset.univ.filter (fun a : Fin n => n - 2 * k + 1 ≤ a.val) := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hgeW a ha⟩
    have hcardU : (v.val ∪ w.val).card = 2 * k := by
      have hcu := Finset.card_union_of_disjoint hdisj
      rw [hcu, v.property, w.property]
      omega
    have hcardH : (Finset.univ.filter
        (fun a : Fin n => n - 2 * k + 1 ≤ a.val)).card ≤ 2 * k - 1 := by
      have hsub : (Finset.univ.filter
          (fun a : Fin n => n - 2 * k + 1 ≤ a.val)).image Fin.val ⊆
          Finset.Ico (n - 2 * k + 1) n := by
        intro m hm
        obtain ⟨a, ha, ham⟩ := Finset.mem_image.mp hm
        have hNa := (Finset.mem_filter.mp ha).2
        rw [Finset.mem_Ico]
        constructor
        · rw [← ham]
          exact hNa
        · rw [← ham]
          exact a.2
      have hleI := Finset.card_le_card hsub
      have hIco : (Finset.Ico (n - 2 * k + 1) n).card = n - (n - 2 * k + 1) :=
        Nat.card_Ico _ _
      have himg : (Finset.univ.filter
          (fun a : Fin n => n - 2 * k + 1 ≤ a.val)).card =
          ((Finset.univ.filter
            (fun a : Fin n => n - 2 * k + 1 ≤ a.val)).image Fin.val).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
      omega
    have hleU : (v.val ∪ w.val).card ≤ (Finset.univ.filter
        (fun a : Fin n => n - 2 * k + 1 ≤ a.val)).card :=
      Finset.card_le_card (by
        intro a ha
        rw [Finset.mem_union] at ha
        rcases ha with h | h
        · exact hsubV h
        · exact hsubW h)
    omega

private def knCp {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (A : Finset (Fin n)) : ℕ :=
  if h : A.card = k then (C ⟨A, h⟩).val + 1 else 0

private theorem knCp_eq {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    {A : Finset (Fin n)} (h : A.card = k) :
    knCp C A = (C ⟨A, h⟩).val + 1 :=
  dite_eq_left h

private theorem knCp_ne {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    {A : Finset (Fin n)} (h : A.card ≠ k) : knCp C A = 0 :=
  dite_eq_right h

private def knPos {n : ℕ} (x : Finset (Bool × Fin n)) : Finset (Fin n) :=
  (x.filter (fun l => l.1 = true)).image Prod.snd

private def knNegIdx {n : ℕ} (x : Finset (Bool × Fin n)) : Finset (Fin n) :=
  (x.filter (fun l => l.1 = false)).image Prod.snd

private def knFp {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (x : Finset (Bool × Fin n)) : ℕ :=
  (Finset.powersetCard k (knPos x)).sup (knCp C)

private def knFm {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (x : Finset (Bool × Fin n)) : ℕ :=
  (Finset.powersetCard k (knNegIdx x)).sup (knCp C)

private theorem knFpFm {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (hk : 0 < k) {x : Finset (Bool × Fin n)} (hcons : knConsistent x)
    (heq : knFp C x = knFm C x) : knFp C x = 0 := by
  classical
  by_contra hpos
  have hpos' : 0 < knFp C x := Nat.pos_of_ne_zero hpos
  have hneP : ((knPos x).powersetCard k).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hsup0 : knFp C x ≤ 0 := by
      unfold knFp
      rw [Finset.sup_le_iff]
      intro B hB
      rw [hempty] at hB
      exact absurd hB (Finset.notMem_empty B)
    omega
  obtain ⟨A, hAmem, hAmax⟩ :=
    Finset.exists_max_image _ (knCp C) hneP
  have hAsup : knFp C x = knCp C A := by
    apply le_antisymm
    · unfold knFp
      rw [Finset.sup_le_iff]
      exact hAmax
    · unfold knFp
      exact Finset.le_sup hAmem
  have hAsub : A ⊆ knPos x := (Finset.mem_powersetCard.mp hAmem).1
  have hAcard : A.card = k := by
    by_contra hne2
    have hzero : knCp C A = 0 := knCp_ne C hne2
    omega
  have hAval : (C ⟨A, hAcard⟩).val + 1 = knFp C x := by
    have hcp := knCp_eq C hAcard
    omega
  have hneM : ((knNegIdx x).powersetCard k).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hsup0 : knFm C x ≤ 0 := by
      unfold knFm
      rw [Finset.sup_le_iff]
      intro B hB
      rw [hempty] at hB
      exact absurd hB (Finset.notMem_empty B)
    omega
  obtain ⟨B, hBmem, hBmax⟩ :=
    Finset.exists_max_image _ (knCp C) hneM
  have hBsup : knFm C x = knCp C B := by
    apply le_antisymm
    · unfold knFm
      rw [Finset.sup_le_iff]
      exact hBmax
    · unfold knFm
      exact Finset.le_sup hBmem
  have hBsub : B ⊆ knNegIdx x := (Finset.mem_powersetCard.mp hBmem).1
  have hBcard : B.card = k := by
    by_contra hne2
    have hzero : knCp C B = 0 := knCp_ne C hne2
    omega
  have hBval : (C ⟨B, hBcard⟩).val + 1 = knFm C x := by
    have hcp := knCp_eq C hBcard
    omega
  have hposmem : ∀ a ∈ A, (true, a) ∈ x := by
    intro a ha
    have haP : a ∈ knPos x := hAsub ha
    obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp haP
    have hl1 : l.1 = true := (Finset.mem_filter.mp hl).2
    have hle : l = (true, a) := Prod.ext hl1 hll
    rw [hle] at hl
    exact Finset.mem_of_mem_filter _ hl
  have hnegmem : ∀ a ∈ B, (false, a) ∈ x := by
    intro a ha
    have haP : a ∈ knNegIdx x := hBsub ha
    obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp haP
    have hl1 : l.1 = false := (Finset.mem_filter.mp hl).2
    have hle : l = (false, a) := Prod.ext hl1 hll
    rw [hle] at hl
    exact Finset.mem_of_mem_filter _ hl
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have ht := hposmem a ha
    have hf := hnegmem a hb
    exact hcons _ ht hf
  have hneAB : A ≠ B := by
    intro heqAB
    have hAne : A.Nonempty := Finset.card_pos.mp (by rw [hAcard]; exact hk)
    obtain ⟨a, ha⟩ := hAne
    have haB : a ∈ B := heqAB ▸ ha
    exact (Finset.disjoint_left.mp hdisj ha) haB
  have hadjG : (kneserGraph n k).Adj ⟨A, hAcard⟩ ⟨B, hBcard⟩ :=
    ⟨hdisj, fun he => hneAB (congrArg Subtype.val he)⟩
  have hCne := C.valid hadjG
  have hCeq : C ⟨A, hAcard⟩ = C ⟨B, hBcard⟩ := by
    apply Fin.ext
    omega
  exact hCne hCeq

private theorem knFp_le {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (x : Finset (Bool × Fin n)) : knFp C x ≤ N := by
  unfold knFp
  rw [Finset.sup_le_iff]
  intro B _
  by_cases hB : B.card = k
  · rw [knCp_eq C hB]
    have hlt := (C ⟨B, hB⟩).isLt
    omega
  · rw [knCp_ne C hB]
    exact Nat.zero_le N

private theorem knFm_le {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (x : Finset (Bool × Fin n)) : knFm C x ≤ N := by
  unfold knFm
  rw [Finset.sup_le_iff]
  intro B _
  by_cases hB : B.card = k
  · rw [knCp_eq C hB]
    have hlt := (C ⟨B, hB⟩).isLt
    omega
  · rw [knCp_ne C hB]
    exact Nat.zero_le N

private theorem knCp_pos_of_card {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N))
    {A : Finset (Fin n)} (h : A.card = k) : 0 < knCp C A := by
  rw [knCp_eq C h]
  omega

private theorem knPos_card_lt_of_fp_zero {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N))
    {x : Finset (Bool × Fin n)} (h0 : knFp C x = 0) :
    (knPos x).card < k := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcon
  have hmem : A ∈ Finset.powersetCard k (knPos x) :=
    Finset.mem_powersetCard.mpr ⟨hAsub, hAcard⟩
  have hle : knCp C A ≤ knFp C x := Finset.le_sup hmem
  have hpos := knCp_pos_of_card C hAcard
  omega

private theorem knNegIdx_card_lt_of_fm_zero {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N))
    {x : Finset (Bool × Fin n)} (h0 : knFm C x = 0) :
    (knNegIdx x).card < k := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcon
  have hmem : A ∈ Finset.powersetCard k (knNegIdx x) :=
    Finset.mem_powersetCard.mpr ⟨hAsub, hAcard⟩
  have hle : knCp C A ≤ knFm C x := Finset.le_sup hmem
  have hpos := knCp_pos_of_card C hAcard
  omega

private theorem knLargeIdx_lt {n k : ℕ} (hk : 0 < k) (h2 : 2 * k ≤ n)
    (f : ℕ) (hf1 : 1 ≤ f) (hfN : f ≤ n - 2 * k + 1) :
    (f - 1) + 2 * (k - 1) < n := by
  omega

private theorem knMinLt {n : ℕ} (a : ℕ) (hn : 0 < n) :
    min a (n - 1) < n := by
  have h := Nat.min_le_right a (n - 1)
  omega

private def knMinIdx {n : ℕ} (x : Finset (Bool × Fin n))
    (hne : x.Nonempty) : Fin n :=
  (x.image Prod.snd).min' (hne.image _)

private def knLabSmall {n : ℕ} (x : Finset (Bool × Fin n))
    (hne : x.Nonempty) (hn : 0 < n) : Bool × Fin n :=
  (decide ((true, knMinIdx x hne) ∈ x),
    ⟨min (x.card - 1) (n - 1), knMinLt _ hn⟩)

private def knLabLargePos {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hk : 0 < k) (h2 : 2 * k ≤ n) (x : Finset (Bool × Fin n))
    (hfp : 1 ≤ knFp C x) : Bool × Fin n :=
  (true, ⟨(knFp C x - 1) + 2 * (k - 1),
    knLargeIdx_lt hk h2 _ hfp (knFp_le C x)⟩)

private def knLabLargeNeg {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hk : 0 < k) (h2 : 2 * k ≤ n) (x : Finset (Bool × Fin n))
    (hfm : 1 ≤ knFm C x) : Bool × Fin n :=
  (false, ⟨(knFm C x - 1) + 2 * (k - 1),
    knLargeIdx_lt hk h2 _ hfm (knFm_le C x)⟩)

private def knLab {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n)
    (x : Finset (Bool × Fin n)) : Bool × Fin n :=
  if _hx : x = ∅ then (true, ⟨n - 1, by omega⟩)
  else if _hsmall : knFp C x = 0 ∧ knFm C x = 0 then
    knLabSmall x (Finset.nonempty_iff_ne_empty.mpr _hx) hn
  else if hpos : knFm C x < knFp C x then
    knLabLargePos C hk h2 x (by omega)
  else
    knLabLargeNeg C hk h2 x (by
      have hfm0 : knFm C x ≠ 0 := by
        intro h0
        apply _hsmall
        refine ⟨?_, h0⟩
        omega
      exact Nat.pos_of_ne_zero hfm0)

private theorem knSmall_card_le {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N))
    {x : Finset (Bool × Fin n)} (hcons : knConsistent x)
    (hfp : knFp C x = 0) (hfm : knFm C x = 0) :
    x.card ≤ 2 * k - 2 := by
  have hp := knPos_card_lt_of_fp_zero C hfp
  have hq := knNegIdx_card_lt_of_fm_zero C hfm
  have hc := knConsistent_card_eq hcons
  omega

private theorem knLarge_or_small {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N)) (hk : 0 < k)
    {x : Finset (Bool × Fin n)} (hcons : knConsistent x) :
    (knFp C x = 0 ∧ knFm C x = 0) ∨
      knFm C x < knFp C x ∨ knFp C x < knFm C x := by
  by_cases heq : knFp C x = knFm C x
  · left
    have h0 := knFpFm C hk hcons heq
    exact ⟨h0, by omega⟩
  · right
    exact lt_or_gt_of_ne (Ne.symm heq)

private theorem knLab_noCompl_empty {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n)
    {y : Finset (Bool × Fin n)} (hconsY : knConsistent y)
    (heq : knLab C hn hk h2 y =
      knNegLabel (knLab C hn hk h2 ∅)) : False := by
  classical
  by_cases hy0 : y = ∅
  · subst hy0
    have hxL := knLab_empty C hn hk h2
    rw [hxL] at heq
    have hfst : (true : Bool) = !true := congrArg Prod.fst heq
    exact (by decide : ¬ ((true : Bool) = !true)) hfst
  · have hyNonempty : y.Nonempty := Finset.nonempty_iff_ne_empty.mpr hy0
    have hval : ((knLab C hn hk h2 y).2).val = n - 1 := by
      have h := congrArg Fin.val (congrArg Prod.snd heq)
      rw [knLab_empty C hn hk h2] at h
      exact h
    rcases knLarge_or_small C hk hconsY with ⟨hfp0, hfm0⟩ | hpos | hneg
    · have hLyv : ((knLab C hn hk h2 y).2).val =
          min (y.card - 1) (n - 1) := by
        have hLy := knLab_small C hn hk h2 hy0 hfp0 hfm0
        simp only [hLy, knLabSmall_snd_val]
      have hne2 := knSmall_val_ne hk h2 hyNonempty
        (knSmall_card_le C hconsY hfp0 hfm0)
      omega
    · have hLyv : ((knLab C hn hk h2 y).2).val =
          (knFp C y - 1) + 2 * (k - 1) := by
        have hlarge : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_pos C hn hk h2 hy0 hlarge hpos (by omega)
        simp only [hLy, knLabLargePos_snd_val]
      have hne2 := knLarge_val_ne hk h2 (knFp C y) (by omega) (knFp_le C y)
      omega
    · have hLyv : ((knLab C hn hk h2 y).2).val =
          (knFm C y - 1) + 2 * (k - 1) := by
        have hlarge : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_neg C hn hk h2 hy0 hlarge (by omega)
          (by omega)
        simp only [hLy, knLabLargeNeg_snd_val]
      have hne2 := knLarge_val_ne hk h2 (knFm C y) (by omega) (knFm_le C y)
      omega

private theorem knLab_noCompl {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n) :
    knNoCompl (knLab C hn hk h2) := by
  classical
  intro x y hconsX hconsY hsub heq
  by_cases hx0 : x = ∅
  · subst hx0
    exact knLab_noCompl_empty C hn hk h2 hconsY heq
  · have hxNonempty : x.Nonempty := Finset.nonempty_iff_ne_empty.mpr hx0
    have hyne : y.Nonempty := by
      obtain ⟨l, hl⟩ := hxNonempty
      exact ⟨l, hsub hl⟩
    have hy0 : y ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hyne
    rcases knLarge_or_small C hk hconsX with ⟨hfp0, hfm0⟩ | hposX | hnegX
    · have hval := congrArg Fin.val (congrArg Prod.snd heq)
      rw [knNegLabel_snd] at hval
      rcases knLarge_or_small C hk hconsY with ⟨hfp0y, hfm0y⟩ | hposY | hnegY
      · have hLx := knLab_small C hn hk h2 hx0 hfp0 hfm0
        have hLy := knLab_small C hn hk h2 hy0 hfp0y hfm0y
        have hLxv : ((knLab C hn hk h2 x).2).val =
            min (x.card - 1) (n - 1) := by
          simp only [hLx, knLabSmall_snd_val]
        have hLyv : ((knLab C hn hk h2 y).2).val =
            min (y.card - 1) (n - 1) := by
          simp only [hLy, knLabSmall_snd_val]
        have hle_x := knSmall_card_le C hconsX hfp0 hfm0
        have hle_y := knSmall_card_le C hconsY hfp0y hfm0y
        have hx1 : 1 ≤ x.card := Finset.one_le_card.mpr hxNonempty
        have hy1 : 1 ≤ y.card := Finset.one_le_card.mpr hyne
        have hcardxy : x.card = y.card := by omega
        have hxy : x = y :=
          Finset.eq_of_subset_of_card_le hsub (by omega)
        have hfst : (knLab C hn hk h2 y).1 =
            !((knLab C hn hk h2 y).1) := by
          have h := congrArg Prod.fst heq
          rw [hxy] at h
          exact h
        cases hbx : (knLab C hn hk h2 y).1 with
        | true =>
          rw [hbx] at hfst
          exact (by decide : ¬ ((true : Bool) = !true)) hfst
        | false =>
          rw [hbx] at hfst
          exact (by decide : ¬ ((false : Bool) = !false)) hfst
      · have hLx := knLab_small C hn hk h2 hx0 hfp0 hfm0
        have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_pos C hn hk h2 hy0 hlargeY hposY
          (by omega)
        have hLxv : ((knLab C hn hk h2 x).2).val =
            min (x.card - 1) (n - 1) := by
          simp only [hLx, knLabSmall_snd_val]
        have hLyv : ((knLab C hn hk h2 y).2).val =
            (knFp C y - 1) + 2 * (k - 1) := by
          simp only [hLy, knLabLargePos_snd_val]
        have hlt := knSmall_val_lt hk hxNonempty
          (knSmall_card_le C hconsX hfp0 hfm0)
        have hge : 2 * (k - 1) ≤ (knFp C y - 1) + 2 * (k - 1) := by
          omega
        omega
      · have hLx := knLab_small C hn hk h2 hx0 hfp0 hfm0
        have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_neg C hn hk h2 hy0 hlargeY (by omega)
          (by omega)
        have hLxv : ((knLab C hn hk h2 x).2).val =
            min (x.card - 1) (n - 1) := by
          simp only [hLx, knLabSmall_snd_val]
        have hLyv : ((knLab C hn hk h2 y).2).val =
            (knFm C y - 1) + 2 * (k - 1) := by
          simp only [hLy, knLabLargeNeg_snd_val]
        have hlt := knSmall_val_lt hk hxNonempty
          (knSmall_card_le C hconsX hfp0 hfm0)
        have hge : 2 * (k - 1) ≤ (knFm C y - 1) + 2 * (k - 1) := by
          omega
        omega
    · have hlargeX : ¬ (knFp C x = 0 ∧ knFm C x = 0) := by
        intro hcon; omega
      have hLx := knLab_large_pos C hn hk h2 hx0 hlargeX hposX
        (by omega)
      rcases knLarge_or_small C hk hconsY with ⟨hfp0y, hfm0y⟩ | hposY | hnegY
      · have hfp_le : knFp C x ≤ knFp C y := knFp_mono C hsub
        have hfm_le : knFm C x ≤ knFm C y := knFm_mono C hsub
        omega
      · have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_pos C hn hk h2 hy0 hlargeY hposY
          (by omega)
        have hfst : (knLab C hn hk h2 y).1 =
            !((knLab C hn hk h2 x).1) :=
          congrArg Prod.fst heq
        rw [hLy, hLx, knLabLargePos_fst, knLabLargePos_fst] at hfst
        exact (by decide : ¬ ((true : Bool) = !true)) hfst
      · have hfp_le : knFp C x ≤ knFp C y := knFp_mono C hsub
        have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_neg C hn hk h2 hy0 hlargeY (by omega)
          (by omega)
        have hval := congrArg Fin.val (congrArg Prod.snd heq)
        rw [knNegLabel_snd] at hval
        have hLxv : ((knLab C hn hk h2 x).2).val =
            (knFp C x - 1) + 2 * (k - 1) := by
          simp only [hLx, knLabLargePos_snd_val]
        have hLyv : ((knLab C hn hk h2 y).2).val =
            (knFm C y - 1) + 2 * (k - 1) := by
          simp only [hLy, knLabLargeNeg_snd_val]
        omega
    · have hlargeX : ¬ (knFp C x = 0 ∧ knFm C x = 0) := by
        intro hcon; omega
      have hLx := knLab_large_neg C hn hk h2 hx0 hlargeX (by omega)
        (by omega)
      rcases knLarge_or_small C hk hconsY with ⟨hfp0y, hfm0y⟩ | hposY | hnegY
      · have hfp_le : knFp C x ≤ knFp C y := knFp_mono C hsub
        have hfm_le : knFm C x ≤ knFm C y := knFm_mono C hsub
        omega
      · have hfm_le : knFm C x ≤ knFm C y := knFm_mono C hsub
        have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_pos C hn hk h2 hy0 hlargeY hposY
          (by omega)
        have hval := congrArg Fin.val (congrArg Prod.snd heq)
        rw [knNegLabel_snd] at hval
        have hLxv : ((knLab C hn hk h2 x).2).val =
            (knFm C x - 1) + 2 * (k - 1) := by
          simp only [hLx, knLabLargeNeg_snd_val]
        have hLyv : ((knLab C hn hk h2 y).2).val =
            (knFp C y - 1) + 2 * (k - 1) := by
          simp only [hLy, knLabLargePos_snd_val]
        omega
      · have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_neg C hn hk h2 hy0 hlargeY (by omega)
          (by omega)
        have hfst : (knLab C hn hk h2 y).1 =
            !((knLab C hn hk h2 x).1) :=
          congrArg Prod.fst heq
        rw [hLy, hLx, knLabLargeNeg_fst, knLabLargeNeg_fst] at hfst
        exact (by decide : ¬ ((false : Bool) = !false)) hfst

private theorem knLab_antipodal {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n) :
    knAntipodal (knLab C hn hk h2) := by
  classical
  intro x hcons hxne
  have hne : x ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hxne
  have hcard : 0 < x.card := Finset.card_pos.mpr hxne
  have hneN : (knNegCell x).Nonempty := by
    apply Finset.card_pos.mp
    rw [knNegCell_card]
    exact hcard
  have hneN' : knNegCell x ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hneN
  have hfpN : knFp C (knNegCell x) = knFm C x := knFp_negCell C x
  have hfmN : knFm C (knNegCell x) = knFp C x := knFm_negCell C x
  rcases knLarge_or_small C hk hcons with ⟨hfp0, hfm0⟩ | hpos | hneg
  · have hfpN0 : knFp C (knNegCell x) = 0 := by rw [hfpN]; exact hfm0
    have hfmN0 : knFm C (knNegCell x) = 0 := by rw [hfmN]; exact hfp0
    have hLx := knLab_small C hn hk h2 hne hfp0 hfm0
    have hLN := knLab_small C hn hk h2 hneN' hfpN0 hfmN0
    rw [hLx, hLN]
    apply Prod.ext
    · simp only [knLabSmall_fst, knNegLabel_fst, knLabSmall_fst,
        knMinIdx_negCell hxne hneN, knTrue_mem_negCell]
      rcases knConsistent_bool_exact hcons
        (knMinIdx_mem hxne) with ⟨ht, hf⟩ | ⟨hf, ht⟩
      · rw [decide_eq_false hf, decide_eq_true ht]
        rfl
      · rw [decide_eq_true hf, decide_eq_false ht]
        rfl
    · apply Fin.ext
      rw [knLabSmall_snd_val, knNegLabel_snd, knLabSmall_snd_val,
        knNegCell_card]
  · have hlarge : ¬ (knFp C x = 0 ∧ knFm C x = 0) := by intro hcon; omega
    have hfp1 : 1 ≤ knFp C x := by omega
    have hLx := knLab_large_pos C hn hk h2 hne hlarge hpos hfp1
    have hlargeN : ¬ (knFp C (knNegCell x) = 0 ∧
        knFm C (knNegCell x) = 0) := by
      rw [hfpN, hfmN]; intro hcon; omega
    have hnegN : ¬ knFm C (knNegCell x) < knFp C (knNegCell x) := by
      rw [hfpN, hfmN]; omega
    have hfmN1 : 1 ≤ knFm C (knNegCell x) := by rw [hfmN]; omega
    have hLN := knLab_large_neg C hn hk h2 hneN' hlargeN hnegN hfmN1
    rw [hLx, hLN]
    unfold knLabLargeNeg knLabLargePos knNegLabel
    dsimp only
    rw [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    rw [Fin.mk.injEq, hfmN]
  · have hlarge : ¬ (knFp C x = 0 ∧ knFm C x = 0) := by intro hcon; omega
    have hfm1 : 1 ≤ knFm C x := by omega
    have hLx := knLab_large_neg C hn hk h2 hne hlarge (by omega) hfm1
    have hlargeN : ¬ (knFp C (knNegCell x) = 0 ∧
        knFm C (knNegCell x) = 0) := by
      rw [hfpN, hfmN]; intro hcon; omega
    have hposN : knFm C (knNegCell x) < knFp C (knNegCell x) := by
      rw [hfpN, hfmN]; omega
    have hfpN1 : 1 ≤ knFp C (knNegCell x) := by rw [hfpN]; omega
    have hLN := knLab_large_pos C hn hk h2 hneN' hlargeN hposN hfpN1
    rw [hLx, hLN]
    unfold knLabLargeNeg knLabLargePos knNegLabel
    dsimp only
    rw [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    rw [Fin.mk.injEq, hfpN]

private theorem knNotColorable {n k : ℕ} (hk : 0 < k) (h2 : 2 * k ≤ n) :
    ¬ (kneserGraph n k).Colorable (n - 2 * k + 1) := by
  intro hC
  obtain ⟨C⟩ := hC
  have hn : 0 < n := by omega
  obtain ⟨x, y, hconsX, hconsY, hsub, heq⟩ :=
    knTucker (knLab C hn hk h2) (knLab_antipodal C hn hk h2)
  exact knLab_noCompl C hn hk h2 x y hconsX hconsY hsub heq

/--
For 0<k and 2k≤n the Kneser graph on k-subsets has chromatic number n-2k+2.
Source: L. Lovasz, JCT A 25 (1978), 319-324, DOI 10.1016/0097-3165(78)90022-5.

Proves `Wanted` entry `kneser_lovasz`.
-/
theorem kneser_lovasz {n k : ℕ} (hk : 0 < k) (h : 2 * k ≤ n) :
    (kneserGraph n k).chromaticNumber = (n - 2 * k + 2 : ℕ∞) := by
  have hcast : (n - 2 * k + 2 : ℕ∞) =
      (((n - 2 * k + 1 : ℕ) : ℕ∞) + 1) := by
    have e1 : ((2 * k : ℕ) : ℕ∞) = 2 * (↑k : ℕ∞) := by push_cast; ring
    have e2 : ((n - 2 * k : ℕ) : ℕ∞) =
        (↑n : ℕ∞) - ((2 * k : ℕ) : ℕ∞) :=
      ENat.natCast_sub n (2 * k)
    have e4 : ((n - 2 * k + 1 : ℕ) : ℕ∞) =
        ((n - 2 * k : ℕ) : ℕ∞) + 1 := by
      push_cast
      ring
    rw [← e1, ← e2, e4]
    ring
  rw [hcast, SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable]
  refine ⟨knUpperColoring hk h, knNotColorable hk h⟩

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted
