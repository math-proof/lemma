import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.SimpleGraph.KneserLovasz.Part8
open Finset
open MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted


namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[kneserGraph_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
lemma kneserGraph_adj_iff
  {n k : ℕ}
  {x y : KneserVertex n k} :
-- imply
  (kneserGraph n k).Adj x y ↔ Disjoint x.val y.val ∧ x ≠ y :=
-- proof
  Iff.rfl

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNegLabel_invol](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNegLabel_invol {n : ℕ} : Function.Involutive (@knNegLabel n) := by
  classical
  intro l
  obtain ⟨b, i⟩ := l
  cases b <;> rfl

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNegLabel_invol_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNegLabel_invol_apply {n : ℕ} (l : Bool × Fin n) :
  knNegLabel (knNegLabel l) = l :=
  knNegLabel_invol l

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNegCell_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNegCell_empty {n : ℕ} :
  knNegCell (∅ : Finset (Bool × Fin n)) = ∅ := by
  classical
  simp [knNegCell]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNegCell_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNegCell_card {n : ℕ} (x : Finset (Bool × Fin n)) :
  (knNegCell x).card = x.card := by
  classical
  simp [knNegCell]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knMem_negCell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knMem_negCell {n : ℕ} {x : Finset (Bool × Fin n)} {l : Bool × Fin n} :
  l ∈ knNegCell x ↔ ∃ m ∈ x, knNegLabel m = l := by
  classical
  rwa [knNegCell]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNegLabel_mem_negCell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNegLabel_mem_negCell {n : ℕ} {x : Finset (Bool × Fin n)}
  {m : Bool × Fin n} (hm : m ∈ x) : knNegLabel m ∈ knNegCell x := by
  classical
  rw [knMem_negCell]
  exact ⟨m, hm, rfl⟩

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNegCell_invol](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNegCell_invol {n : ℕ} (x : Finset (Bool × Fin n)) :
  knNegCell (knNegCell x) = x := by
  classical
  ext l
  simp only [knMem_negCell]
  constructor
  · rintro ⟨m, hm, hml⟩
    obtain ⟨m', hm', hm'm⟩ := hm
    have hme : m' = l := by
      have h1 : knNegLabel (knNegLabel m') = knNegLabel m :=
        congrArg knNegLabel hm'm
      rwa [knNegLabel_invol_apply, hml] at h1
    rwa [← hme]
  · intro hl
    exact ⟨knNegLabel l, ⟨l, hl, rfl⟩, knNegLabel_invol_apply l⟩

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knMem_subset_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knMem_subset_top {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  {x : Finset (Bool × Fin n)} (hx : x ∈ σ) : x ⊆ knTop σ := by
  classical
  have h := Finset.le_sup (s := σ) (f := id) hx
  simpa [knTop] using h

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTop_sup_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTop_sup_le {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  {m : Finset (Bool × Fin n)} (h : ∀ x ∈ σ, x ⊆ m) : knTop σ ⊆ m := by
  classical
  have h2 : σ.sup id ≤ m := by
    rw [Finset.sup_le_iff]
    intro b hb
    simpa using h b hb
  simpa [knTop] using h2

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knChain_top_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knChain_top_mem {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (h : knChain σ) : knTop σ ∈ σ := by
  classical
  obtain ⟨hne, _, hchain⟩ := h
  obtain ⟨m, hmσ, hmax⟩ := Finset.exists_max_image σ Finset.card hne
  have hsub : ∀ x ∈ σ, x ⊆ m := by
    intro x hx
    obtain hsub | hsub := hchain x hx m hmσ
    · exact hsub
    · have hle : x.card ≤ m.card := hmax x hx
      have hme : m = x := Finset.eq_of_subset_of_card_le hsub hle
      subst hme
      exact Subset.rfl
  have htop : knTop σ = m := by
    apply le_antisymm
    · exact knTop_sup_le σ hsub
    · exact knMem_subset_top σ hmσ
  rwa [htop]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knChain_eq_of_mem_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knChain_eq_of_mem_card_eq {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (hchain : knIsChain σ) {a b : Finset (Bool × Fin n)}
  (ha : a ∈ σ) (hb : b ∈ σ) (hcard : a.card = b.card) : a = b := by
  classical
  obtain h | h := hchain a ha b hb
  · exact Finset.eq_of_subset_of_card_le h (by omega)
  · exact (Finset.eq_of_subset_of_card_le h (by omega)).symm

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knChain_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knChain_card_le {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (h : knChain σ) : σ.card ≤ (knTop σ).card + 1 := by
  classical
  obtain ⟨_, _, hchain⟩ := h
  have hmaps : Set.MapsTo Finset.card (↑σ : Set (Finset (Bool × Fin n)))
    (↑(Finset.range ((knTop σ).card + 1)) : Set ℕ) := by
    intro x hx
    have hxσ : x ∈ σ := Finset.mem_coe.mp hx
    have hsub : x ⊆ knTop σ := knMem_subset_top σ hxσ
    have hcc := Finset.card_le_card hsub
    rw [Finset.mem_coe, Finset.mem_range]
    omega
  have hinj : Set.InjOn Finset.card (↑σ : Set (Finset (Bool × Fin n))) := by
    intro a ha b hb hab
    have ha' : a ∈ σ := Finset.mem_coe.mp ha
    have hb' : b ∈ σ := Finset.mem_coe.mp hb
    exact knChain_eq_of_mem_card_eq σ hchain ha' hb' hab
  have hle := Finset.card_le_card_of_injOn Finset.card hmaps hinj
  rwa [Finset.card_range] at hle

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knChain_insert](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knChain_insert {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  {v : Finset (Bool × Fin n)} (hchain : knChain σ) (hcons : knConsistent v)
  (hcomp : ∀ x ∈ σ, x ⊆ v ∨ v ⊆ x) : knChain (insert v σ) := by
  classical
  obtain ⟨_, hconsσ, hch⟩ := hchain
  refine ⟨Finset.insert_nonempty v σ, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_insert] at hx
    obtain rfl | hx := hx
    · exact hcons
    · exact hconsσ x hx
  · intro a ha b hb
    rw [Finset.mem_insert] at ha hb
    obtain rfl | ha <;> rcases hb with rfl | hb := ha
    · exact Or.inl Subset.rfl
    · exact (hcomp b hb).symm
    · exact hcomp a ha
    · exact hch a ha b hb

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTop_insert](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTop_insert {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (v : Finset (Bool × Fin n)) : knTop (insert v σ) = v ∪ knTop σ := by
  classical
  have h : (insert v σ).sup id = id v ⊔ σ.sup id := Finset.sup_insert
  have h2 : id v ⊔ σ.sup id = v ∪ knTop σ := by
    simp [knTop, Finset.sup_eq_union]
  unfold knTop
  rwa [h]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTop_insert_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTop_insert_of_subset {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (v : Finset (Bool × Fin n)) (h : v ⊆ knTop σ) :
  knTop (insert v σ) = knTop σ := by
  classical
  rw [knTop_insert]
  exact Finset.union_eq_right.mpr h

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTop_insert_of_supset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTop_insert_of_supset {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (v : Finset (Bool × Fin n)) (h : knTop σ ⊆ v) :
  knTop (insert v σ) = v := by
  classical
  rw [knTop_insert]
  exact Finset.union_eq_left.mpr h

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knImageCard_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knImageCard_subset {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) :
  σ.image Finset.card ⊆ Finset.range ((knTop σ).card + 1) := by
  classical
  intro j hj
  rw [Finset.mem_image] at hj
  obtain ⟨x, hx, rfl⟩ := hj
  rw [Finset.mem_range]
  have hle := Finset.card_le_card (knMem_subset_top σ hx)
  omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knImageCard_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knImageCard_card {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (h : knChain σ) : (σ.image Finset.card).card = σ.card := by
  classical
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have ha' : a ∈ σ := Finset.mem_coe.mp ha
  have hb' : b ∈ σ := Finset.mem_coe.mp hb
  exact knChain_eq_of_mem_card_eq σ h.2.2 ha' hb' hab

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knHappy_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knHappy_card_eq {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knHappy σ L) :
  σ.card = (knTop σ).card ∨ σ.card = (knTop σ).card + 1 := by
  classical
  obtain ⟨hchain, hsub⟩ := h
  have h1 : (knTop σ).card ≤ (knImg σ L).card := Finset.card_le_card hsub
  have h2 : (knImg σ L).card ≤ σ.card := by
    unfold knImg
    exact Finset.card_image_le
  have h3 : σ.card ≤ (knTop σ).card + 1 := knChain_card_le σ hchain
  omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTight_image](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTight_image {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) :
  knImg σ L = knTop σ := by
  classical
  obtain ⟨⟨_, hsub⟩, hcard⟩ := h
  have h2 : (knImg σ L).card ≤ (knTop σ).card := by
    calc (knImg σ L).card ≤ σ.card := by
      unfold knImg
      exact Finset.card_image_le
      _ = (knTop σ).card := hcard
  have heq := Finset.eq_of_subset_of_card_le hsub h2
  exact heq.symm

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTight_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTight_injOn {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) :
  Set.InjOn L (↑σ : Set (Finset (Bool × Fin n))) := by
  classical
  have htop : knImg σ L = knTop σ := knTight_image σ L h
  obtain ⟨_, hcard⟩ := h
  have h2 : (σ.image L).card = σ.card := by
    have hcc := congrArg Finset.card htop
    simp only [knImg] at hcc
    omega
  exact Finset.injOn_of_card_image_eq h2

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTight_top_card_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTight_top_card_pos {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) :
  1 ≤ (knTop σ).card := by
  classical
  obtain ⟨⟨⟨hne, _, _⟩, _⟩, hcard⟩ := h
  obtain ⟨x, hx⟩ := hne
  have h1 : 1 ≤ σ.card := Finset.one_le_card.mpr ⟨x, hx⟩
  omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLoose_imageCard](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLoose_imageCard {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L) :
  σ.image Finset.card = Finset.range ((knTop σ).card + 1) := by
  classical
  obtain ⟨⟨hchain, _⟩, hcard⟩ := h
  have hsub := knImageCard_subset σ
  have hcc := knImageCard_card σ hchain
  have hreq : (σ.image Finset.card).card = (Finset.range ((knTop σ).card + 1)).card := by
    rw [hcc, hcard, Finset.card_range]
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLoose_has_level](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLoose_has_level {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L) {j : ℕ}
  (hj : j ≤ (knTop σ).card) : ∃ x ∈ σ, x.card = j := by
  classical
  have hmem : j ∈ σ.image Finset.card := by
    rw [knLoose_imageCard σ L h, Finset.mem_range]
    omega
  obtain ⟨x, hx, hxj⟩ := Finset.mem_image.mp hmem
  exact ⟨x, hx, hxj⟩

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLoose_empty_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLoose_empty_mem {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L) : ∅ ∈ σ := by
  classical
  obtain ⟨x, hx, hxj⟩ := knLoose_has_level σ L h (Nat.zero_le _)
  have hx0 : x = ∅ := Finset.card_eq_zero.mp hxj
  rwa [hx0] at hx

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTight_missing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTight_missing {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) :
  ∃ j, j ≤ (knTop σ).card ∧
    σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j := by
  classical
  obtain ⟨⟨hchain, _⟩, hcard⟩ := h
  have hsub : σ.image Finset.card ⊆ Finset.range ((knTop σ).card + 1) :=
    knImageCard_subset σ
  have hcc : (σ.image Finset.card).card = (knTop σ).card := by
    have hcc2 := knImageCard_card σ hchain
    omega
  have hsdiff : ((Finset.range ((knTop σ).card + 1)) \ σ.image Finset.card).card = 1 := by
    have hunion := Finset.sdiff_union_of_subset hsub
    have hdisj : Disjoint ((Finset.range ((knTop σ).card + 1)) \ σ.image Finset.card)
      (σ.image Finset.card) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp hx1).2 hx2
    have hcu := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_range] at hcu
    omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hsdiff
  have hjmem : j ∈ Finset.range ((knTop σ).card + 1) := by
    have hmem : j ∈ ({j} : Finset ℕ) := Finset.mem_singleton_self j
    rw [← hj] at hmem
    exact (Finset.mem_sdiff.mp hmem).1
  have hjeq : σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j := by
    ext x
    rw [Finset.mem_erase]
    constructor
    · intro hx
      refine ⟨?_, hsub hx⟩
      intro hxj
      have hmem : j ∈ (Finset.range ((knTop σ).card + 1)) \ σ.image Finset.card := by
        rw [hj]
        exact Finset.mem_singleton_self j
      have hxj' : j ∈ σ.image Finset.card := by
        rwa [← hxj]
      exact (Finset.mem_sdiff.mp hmem).2 hxj'
    · intro hx
      obtain ⟨hne, hxr⟩ := hx
      by_contra hxnot
      have hmem : x ∈ (Finset.range ((knTop σ).card + 1)) \ σ.image Finset.card :=
        Finset.mem_sdiff.mpr ⟨hxr, hxnot⟩
      rw [hj] at hmem
      exact hne (Finset.mem_singleton.mp hmem)
  rw [Finset.mem_range] at hjmem
  exact ⟨j, by omega, hjeq⟩

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTight_no_level](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTight_no_level {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (_h : knTight σ L) {j : ℕ}
  (hj : σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j)
  {x : Finset (Bool × Fin n)} (hx : x ∈ σ) : x.card ≠ j := by
  classical
  intro hcx
  have hmem : x.card ∈ (Finset.range ((knTop σ).card + 1)).erase j := by
    rw [← hj]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  exact (Finset.mem_erase.mp hmem).1 hcx

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTight_has_level](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTight_has_level {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (_h : knTight σ L) {j : ℕ}
  (hj : σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j)
  {m : ℕ} (hm : m ≤ (knTop σ).card) (hmj : m ≠ j) : ∃ x ∈ σ, x.card = m := by
  classical
  have hmem : m ∈ σ.image Finset.card := by
    rw [hj, Finset.mem_erase, Finset.mem_range]
    exact ⟨hmj, by omega⟩
  obtain ⟨x, hx, hxj⟩ := Finset.mem_image.mp hmem
  exact ⟨x, hx, hxj⟩

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTight_empty_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTight_empty_iff {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) {j : ℕ}
  (hj : σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j) :
  (∅ ∈ σ) ↔ j ≠ 0 := by
  classical
  constructor
  · intro hmem heq
    subst heq
    exact knTight_no_level σ L h hj hmem Finset.card_empty
  · intro hne
    obtain ⟨x, hx, hxj⟩ := knTight_has_level σ L h hj (Nat.zero_le _) (Ne.symm hne)
    have hx0 : x = ∅ := Finset.card_eq_zero.mp hxj
    rwa [hx0] at hx

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knSdiff_card_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knSdiff_card_two {α : Type*} [DecidableEq α] {a b : Finset α}
  (hab : a ⊆ b) (hcard : b.card = a.card + 2) : (b \ a).card = 2 := by
  classical
  have hunion := Finset.sdiff_union_of_subset hab
  have hdisj : Disjoint (b \ a) a := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx1).2 hx2
  have hcu := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hcu
  omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knInsert_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knInsert_injOn {α : Type*} [DecidableEq α] {a b : Finset α} :
  Set.InjOn (fun x => insert x a) (↑(b \ a) : Set α) := by
  classical
  intro x hx y hy hxy
  have hxna : x ∉ a := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hx)).2
  have hxy' : insert x a = insert y a := hxy
  have hxmem : x ∈ insert y a := by
    rw [← hxy']
    exact Finset.mem_insert_self x a
  obtain heq | hcon := Finset.mem_insert.mp hxmem
  · exact heq
  · exact absurd hcon hxna

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knBetween_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knBetween_mem {α : Type*} [DecidableEq α] {a b : Finset α}
  (hab : a ⊆ b) {v : Finset α} :
  v ∈ (b \ a).image (fun x => insert x a) ↔
    a ⊆ v ∧ v ⊆ b ∧ v.card = a.card + 1 := by
  classical
  constructor
  · intro hv
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hv
    have hxmem := Finset.mem_sdiff.mp hx
    have hxa : x ∉ a := hxmem.2
    have hxb : x ∈ b := hxmem.1
    refine ⟨?_, ?_, ?_⟩
    · rw [← hxeq]
      exact Finset.subset_insert x a
    · rw [← hxeq]
      exact Finset.insert_subset hxb hab
    · rw [← hxeq]
      exact Finset.card_insert_of_notMem hxa
  · intro hv
    obtain ⟨hav1, hbv, hvcard⟩ := hv
    have hva1 : (v \ a).card = 1 := by
      have hunion := Finset.sdiff_union_of_subset hav1
      have hdisj : Disjoint (v \ a) a := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact (Finset.mem_sdiff.mp hx1).2 hx2
      have hcu := Finset.card_union_of_disjoint hdisj
      rw [hunion] at hcu
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hva1
    have hxmem : x ∈ v ∧ x ∉ a := by
      have hself : x ∈ ({x} : Finset α) := Finset.mem_singleton_self x
      rw [← hx] at hself
      exact ⟨(Finset.mem_sdiff.mp hself).1, (Finset.mem_sdiff.mp hself).2⟩
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_sdiff.mpr ⟨hbv hxmem.1, hxmem.2⟩, ?_⟩
    show insert x a = v
    apply le_antisymm
    · exact Finset.insert_subset hxmem.1 hav1
    · intro y hy
      show y ∈ insert x a
      rw [Finset.mem_insert]
      by_cases hya : y ∈ a
      · exact Or.inr hya
      · left
        have hmem : y ∈ v \ a := Finset.mem_sdiff.mpr ⟨hy, hya⟩
        rw [hx] at hmem
        exact Finset.mem_singleton.mp hmem

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knBetween_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knBetween_card {α : Type*} [DecidableEq α] {a b : Finset α}
  (hab : a ⊆ b) (hcard : b.card = a.card + 2) :
  ((b \ a).image (fun x => insert x a)).card = 2 := by
  classical
  rw [Finset.card_image_of_injOn knInsert_injOn]
  exact knSdiff_card_two hab hcard

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knMem_out](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knMem_out {n : ℕ} {σ : Finset (Finset (Bool × Fin n))}
  {L : Finset (Bool × Fin n) → Bool × Fin n} {v : Finset (Bool × Fin n)} :
  v ∈ knOut σ L ↔
    v ∉ σ ∧ knChain (insert v σ) ∧ knTop (insert v σ) ⊆ knImg σ L := by
  classical
  unfold knOut
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knMem_in](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knMem_in {n : ℕ} {σ : Finset (Finset (Bool × Fin n))}
  {L : Finset (Bool × Fin n) → Bool × Fin n} {w : Finset (Bool × Fin n)} :
  w ∈ knIn σ L ↔
    w ∈ σ ∧ knHappy (σ.erase w) L ∧ knTop σ ⊆ knImg (σ.erase w) L := by
  classical
  unfold knIn
  rw [Finset.mem_filter]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knOut_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knOut_neighbor {n : ℕ} {σ : Finset (Finset (Bool × Fin n))}
  {L : Finset (Bool × Fin n) → Bool × Fin n} (hσ : knHappy σ L)
  {v : Finset (Bool × Fin n)} (hv : v ∈ knOut σ L) :
  (knG L).Adj σ (insert v σ) := by
  classical
  rw [knMem_out] at hv
  obtain ⟨hvn, hchain, htop⟩ := hv
  refine ⟨hσ, ⟨hchain, ?_⟩, Or.inl ⟨v, hvn, rfl, htop⟩⟩
  exact htop.trans (Finset.image_subset_image (Finset.subset_insert v σ))

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knIn_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knIn_neighbor {n : ℕ} {σ : Finset (Finset (Bool × Fin n))}
  {L : Finset (Bool × Fin n) → Bool × Fin n} (hσ : knHappy σ L)
  {w : Finset (Bool × Fin n)} (hw : w ∈ knIn σ L) :
  (knG L).Adj σ (σ.erase w) := by
  classical
  rw [knMem_in] at hw
  obtain ⟨hwm, hhappy, htop⟩ := hw
  refine ⟨hσ, hhappy, Or.inr ⟨w, Finset.notMem_erase w σ, ?_, htop⟩⟩
  exact (Finset.insert_erase hwm).symm

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNeighbor_out_or_in](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNeighbor_out_or_in {n : ℕ} {σ τ : Finset (Finset (Bool × Fin n))}
  {L : Finset (Bool × Fin n) → Bool × Fin n} (h : (knG L).Adj σ τ) :
  (∃ v ∈ knOut σ L, insert v σ = τ) ∨ (∃ w ∈ knIn σ L, σ.erase w = τ) := by
  classical
  obtain ⟨_, hτ, hdoor⟩ := h
  obtain ⟨v, hvn, heq, htop⟩ | ⟨w, hwn, heq, htop⟩ := hdoor
  · left
    have hchain : knChain (insert v σ) := by
      rwa [← heq]
    have htop' : knTop (insert v σ) ⊆ knImg σ L := by
      rwa [← heq]
    have hmem : v ∈ knOut σ L := by
      rw [knMem_out]
      exact ⟨hvn, hchain, htop'⟩
    exact ⟨v, hmem, heq.symm⟩
  · right
    have hwm : w ∈ σ := by
      rw [heq]
      exact Finset.mem_insert_self w τ
    have herase : σ.erase w = τ := by
      rw [heq]
      exact Finset.erase_insert hwn
    have hhappy : knHappy (σ.erase w) L := by
      rwa [herase]
    have htop' : knTop σ ⊆ knImg (σ.erase w) L := by
      rwa [herase]
    have hmem : w ∈ knIn σ L := by
      rw [knMem_in]
      exact ⟨hwm, hhappy, htop'⟩
    exact ⟨w, hmem, herase⟩

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNeighborFinset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNeighborFinset_eq {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (hσ : knHappy σ L) :
  (knG L).neighborFinset σ =
    (knOut σ L).image (fun v => insert v σ) ∪
      (knIn σ L).image (fun w => σ.erase w) := by
  classical
  ext τ
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_union]
  constructor
  · intro hadj
    obtain ⟨v, hv, heqv⟩ | ⟨w, hw, heqw⟩ := knNeighbor_out_or_in hadj
    · left
      exact Finset.mem_image.mpr ⟨v, hv, heqv⟩
    · right
      exact Finset.mem_image.mpr ⟨w, hw, heqw⟩
  · intro hmem
    obtain hmem | hmem := hmem
    · obtain ⟨v, hv, heqv⟩ := Finset.mem_image.mp hmem
      rw [← heqv]
      exact knOut_neighbor hσ hv
    · obtain ⟨w, hw, heqw⟩ := Finset.mem_image.mp hmem
      rw [← heqw]
      exact knIn_neighbor hσ hw

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knOutIn_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knOutIn_disjoint {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) :
  Disjoint ((knOut σ L).image (fun v => insert v σ))
    ((knIn σ L).image (fun w => σ.erase w)) := by
  classical
  rw [Finset.disjoint_left]
  intro τ h1 h2
  obtain ⟨v, hv, heqv⟩ := Finset.mem_image.mp h1
  obtain ⟨w, hw, heqw⟩ := Finset.mem_image.mp h2
  rw [knMem_out] at hv
  rw [knMem_in] at hw
  have h1c : τ.card = σ.card + 1 := by
    rw [← heqv]
    exact Finset.card_insert_of_notMem hv.1
  have h2c : (σ.erase w).card = σ.card - 1 := Finset.card_erase_of_mem hw.1
  have heqw' : σ.erase w = τ := heqw
  rw [heqw'] at h2c
  omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knInsert_injOn_out](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knInsert_injOn_out {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) :
  Set.InjOn (fun v => insert v σ) {v | v ∉ σ} := by
  classical
  intro u hu v hv huv
  have hu' : u ∉ σ := hu
  have hv' : v ∉ σ := hv
  have huv' : insert u σ = insert v σ := huv
  have hmem : u ∈ insert v σ := by
    rw [← huv']
    exact Finset.mem_insert_self u σ
  obtain heq | hcon := Finset.mem_insert.mp hmem
  · exact heq
  · exact absurd hcon hu'

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knOut_image_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knOut_image_card {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) :
  ((knOut σ L).image (fun v => insert v σ)).card = (knOut σ L).card := by
  classical
  apply Finset.card_image_of_injOn
  refine Set.InjOn.mono ?_ (knInsert_injOn_out σ)
  intro x hx
  change x ∉ σ
  have hxo : x ∈ knOut σ L := Finset.mem_coe.mp hx
  exact (knMem_out.mp hxo).1

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knErase_injOn_in](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knErase_injOn_in {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) :
  Set.InjOn (fun w => σ.erase w) (↑σ : Set (Finset (Bool × Fin n))) := by
  classical
  intro a ha b hb hab
  have ha' : a ∈ σ := Finset.mem_coe.mp ha
  have hb' : b ∈ σ := Finset.mem_coe.mp hb
  by_contra hne0
  have hmem : a ∈ σ.erase b := Finset.mem_erase.mpr ⟨hne0, ha'⟩
  have hab' : σ.erase a = σ.erase b := hab
  rw [← hab'] at hmem
  exact Finset.notMem_erase a σ hmem

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knIn_image_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knIn_image_card {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) :
  ((knIn σ L).image (fun w => σ.erase w)).card = (knIn σ L).card := by
  classical
  apply Finset.card_image_of_injOn
  refine Set.InjOn.mono ?_ (knErase_injOn_in σ)
  intro x hx
  have hxo : x ∈ knIn σ L := Finset.mem_coe.mp hx
  exact Finset.mem_coe.mpr (knMem_in.mp hxo).1

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knDegree_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knDegree_eq {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (hσ : knHappy σ L) :
  (knG L).degree σ = (knOut σ L).card + (knIn σ L).card := by
  classical
  have hne := knNeighborFinset_eq σ L hσ
  have hdisj := knOutIn_disjoint σ L
  have hcard := Finset.card_union_of_disjoint hdisj
  have ho := knOut_image_card σ L
  have hi := knIn_image_card σ L
  unfold SimpleGraph.degree
  rw [hne, hcard, ho, hi]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knDegree_nothappy](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knDegree_nothappy {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (hσ : ¬ knHappy σ L) :
  (knG L).degree σ = 0 := by
  classical
  have hempty : (knG L).neighborFinset σ = ∅ := by
    ext τ
    simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
    intro hadj
    obtain ⟨hs, _, _⟩ := hadj
    exact hσ hs
  unfold SimpleGraph.degree
  rw [hempty, Finset.card_empty]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTight_no_in](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTight_no_in {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) :
  knIn σ L = ∅ := by
  classical
  ext w
  simp only [knMem_in, Finset.notMem_empty, iff_false]
  intro hw
  obtain ⟨hwm, _, htopsub⟩ := hw
  obtain ⟨hhappy, hcard⟩ := h
  obtain ⟨x, hx⟩ := hhappy.1.1
  have hpos : 1 ≤ σ.card := Finset.one_le_card.mpr ⟨x, hx⟩
  have h1 : (knTop σ).card ≤ (knImg (σ.erase w) L).card :=
    Finset.card_le_card htopsub
  have h2 : (knImg (σ.erase w) L).card ≤ (σ.erase w).card := by
    unfold knImg
    exact Finset.card_image_le
  have h3 : (σ.erase w).card = σ.card - 1 := Finset.card_erase_of_mem hwm
  omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTight_out_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTight_out_card_eq {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) {j : ℕ}
  (hj : σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j)
  {v : Finset (Bool × Fin n)} (hv : v ∈ knOut σ L) : v.card = j := by
  classical
  have himg : knImg σ L = knTop σ := knTight_image σ L h
  rw [knMem_out] at hv
  obtain ⟨hvn, hchainI, htopI⟩ := hv
  have hsub : v ⊆ knTop σ := by
    have hunion : v ∪ knTop σ ⊆ knTop σ := by
      rw [← knTop_insert]
      rwa [himg] at htopI
    exact Finset.subset_union_left.trans hunion
  have hle : v.card ≤ (knTop σ).card := Finset.card_le_card hsub
  by_contra hne
  obtain ⟨x, hx, hxc⟩ := knTight_has_level σ L h hj hle hne
  obtain ⟨_, _, hisch⟩ := hchainI
  have hxv : x ∈ insert v σ := Finset.mem_insert_of_mem hx
  have hvv : v ∈ insert v σ := Finset.mem_insert_self v σ
  have heq : x = v := knChain_eq_of_mem_card_eq _ hisch hxv hvv hxc
  rw [heq] at hx
  exact hvn hx

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTight_out_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTight_out_mem {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L)
  {v : Finset (Bool × Fin n)} (hsub : v ⊆ knTop σ)
  (hcomp : ∀ x ∈ σ, x ⊆ v ∨ v ⊆ x) (hvn : v ∉ σ) : v ∈ knOut σ L := by
  classical
  obtain ⟨hhappy, _⟩ := h
  obtain ⟨hchain, hsub2⟩ := hhappy
  have htopmem : knTop σ ∈ σ := knChain_top_mem σ hchain
  have hconsσ : ∀ x ∈ σ, knConsistent x := hchain.2.1
  have hconTop : knConsistent (knTop σ) := hconsσ _ htopmem
  have hconv : knConsistent v := by
    intro l hl hnl
    exact hconTop l (hsub hl) (hsub hnl)
  have hchainI := knChain_insert σ hchain hconv hcomp
  rw [knMem_out]
  refine ⟨hvn, hchainI, ?_⟩
  rwa [knTop_insert_of_subset σ v hsub]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTight_out_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTight_out_zero {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) {j : ℕ}
  (hj : σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j)
  (hj0 : j = 0) : knOut σ L = {∅} := by
  classical
  ext v
  rw [Finset.mem_singleton]
  constructor
  · intro hv
    have hcv := knTight_out_card_eq σ L h hj hv
    rw [hj0] at hcv
    exact Finset.card_eq_zero.mp hcv
  · intro hv
    rw [hv]
    refine knTight_out_mem σ L h (Finset.empty_subset _) ?_ ?_
    · intro x _
      exact Or.inr (Finset.empty_subset x)
    · intro hcon
      have hne := knTight_no_level σ L h hj hcon
      rw [hj0] at hne
      exact hne Finset.card_empty

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTight_out_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTight_out_two {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) {j : ℕ}
  (hj : σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j)
  (hjle : j ≤ (knTop σ).card) (hjge : 1 ≤ j) : (knOut σ L).card = 2 := by
  classical
  have hchain : knChain σ := h.1.1
  have hcard : σ.card = (knTop σ).card := h.2
  have hisch : knIsChain σ := hchain.2.2
  have htop_hit : (knTop σ).card ∈ σ.image Finset.card :=
    Finset.mem_image.mpr ⟨knTop σ, knChain_top_mem σ hchain, rfl⟩
  rw [hj] at htop_hit
  have hkj : (knTop σ).card ≠ j := (Finset.mem_erase.mp htop_hit).1
  have hjlt : j + 1 ≤ (knTop σ).card := by omega
  obtain ⟨a, ha_mem, ha_card⟩ :=
    knTight_has_level (m := j - 1) σ L h hj (by omega) (by omega)
  obtain ⟨b, hb_mem, hb_card⟩ :=
    knTight_has_level (m := j + 1) σ L h hj hjlt (by omega)
  have hab : a ⊆ b := by
    obtain hsub | hsub := hisch a ha_mem b hb_mem
    · exact hsub
    · exfalso
      have hle := Finset.card_le_card hsub
      omega
  have hOut_eq : knOut σ L = (b \ a).image (fun x => insert x a) := by
    ext v
    rw [knBetween_mem hab]
    constructor
    · intro hv
      have hvj := knTight_out_card_eq σ L h hj hv
      rw [knMem_out] at hv
      obtain ⟨_, hchainI, _⟩ := hv
      obtain ⟨_, _, hischI⟩ := hchainI
      have hav : a ⊆ v := by
        rcases hischI a (Finset.mem_insert_of_mem ha_mem) v
          (Finset.mem_insert_self v σ) with hsub | hsub
        · exact hsub
        · exfalso
          have hle := Finset.card_le_card hsub
          omega
      have hvb : v ⊆ b := by
        rcases hischI v (Finset.mem_insert_self v σ) b
          (Finset.mem_insert_of_mem hb_mem) with hsub | hsub
        · exact hsub
        · exfalso
          have hle := Finset.card_le_card hsub
          omega
      refine ⟨hav, hvb, ?_⟩
      omega
    · intro hv
      obtain ⟨hav, hvb, hvc⟩ := hv
      have hvj : v.card = j := by omega
      have hsub_top : v ⊆ knTop σ :=
        hvb.trans (knMem_subset_top σ hb_mem)
      have hcomp : ∀ x ∈ σ, x ⊆ v ∨ v ⊆ x := by
        intro x hx
        have hxj : x.card ≠ j := knTight_no_level σ L h hj hx
        have hxa := hisch x hx a ha_mem
        have hxb := hisch x hx b hb_mem
        by_cases hlt : x.card < v.card
        · left
          obtain hsub | hsub := hxa
          · exact hsub.trans hav
          · have hle1 := Finset.card_le_card hsub
            have heq : x.card = a.card := by omega
            have hxeq : x = a :=
              knChain_eq_of_mem_card_eq σ hisch hx ha_mem heq
            rwa [hxeq]
        · right
          have hlt' : v.card < x.card := by omega
          obtain hsub | hsub := hxb
          · have hle2 := Finset.card_le_card hsub
            have heq : x.card = b.card := by omega
            have hxeq : x = b :=
              knChain_eq_of_mem_card_eq σ hisch hx hb_mem heq
            rwa [hxeq]
          · exact hvb.trans hsub
      have hvn : v ∉ σ := by
        intro hcon
        exact knTight_no_level σ L h hj hcon hvj
      exact knTight_out_mem σ L h hsub_top hcomp hvn
  rw [hOut_eq]
  exact knBetween_card hab (by omega)

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTight_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTight_degree {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) :
  ((knG L).degree σ = 1 ∧ ∅ ∉ σ) ∨ ((knG L).degree σ = 2 ∧ ∅ ∈ σ) := by
  classical
  obtain ⟨hhappy, hcard⟩ := h
  obtain ⟨j, hjle, hjeq⟩ := knTight_missing σ L ⟨hhappy, hcard⟩
  have hin : (knIn σ L).card = 0 := by
    rw [knTight_no_in σ L ⟨hhappy, hcard⟩, Finset.card_empty]
  have hdeg : (knG L).degree σ = (knOut σ L).card := by
    rw [knDegree_eq σ L hhappy, hin, add_zero]
  by_cases hj0 : j = 0
  · left
    have hout : knOut σ L = {∅} :=
      knTight_out_zero σ L ⟨hhappy, hcard⟩ hjeq hj0
    have hempty : ∅ ∉ σ := by
      have hiff := knTight_empty_iff σ L ⟨hhappy, hcard⟩ hjeq
      intro hcon
      have hne := hiff.mp hcon
      rw [hj0] at hne
      exact hne rfl
    rw [hdeg, hout, Finset.card_singleton]
    exact ⟨rfl, hempty⟩
  · right
    have hjge : 1 ≤ j := by omega
    have hout : (knOut σ L).card = 2 :=
      knTight_out_two σ L ⟨hhappy, hcard⟩ hjeq hjle hjge
    have hempty : ∅ ∈ σ := by
      have hiff := knTight_empty_iff σ L ⟨hhappy, hcard⟩ hjeq
      apply hiff.mpr
      omega
    rw [hdeg, hout]
    exact ⟨rfl, hempty⟩

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knSum_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knSum_two {α : Type*} (s : Finset α) (g : α → ℕ)
  (hge : ∀ y ∈ s, 1 ≤ g y) (hsum : ∑ y ∈ s, g y = s.card + 1) :
  ∃ l0 ∈ s, g l0 = 2 ∧ ∀ l ∈ s, l ≠ l0 → g l = 1 := by
  classical
  have hex : ∃ l0 ∈ s, 2 ≤ g l0 := by
    by_contra hcon
    have hall : ∀ l ∈ s, g l = 1 := by
      intro l hl
      have h1 := hge l hl
      have h2 : ¬ 2 ≤ g l := fun hle => hcon ⟨l, hl, hle⟩
      omega
    have hsum1 : ∑ y ∈ s, g y = s.card := by
      calc ∑ y ∈ s, g y = ∑ y ∈ s, 1 :=
        Finset.sum_congr rfl (fun l hl => hall l hl)
        _ = s.card := by simp
    omega
  obtain ⟨l0, hl0, hg0⟩ := hex
  have huniq : ∀ l1 ∈ s, ∀ l2 ∈ s, 2 ≤ g l1 → 2 ≤ g l2 → l1 = l2 := by
    intro l1 hl1 l2 hl2 hg1 hg2
    by_contra hne
    have hsub : ({l1, l2} : Finset α) ⊆ s := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl := hx
      · exact hl1
      · exact hl2
    have hpair_ne : l1 ≠ l2 := hne
    have h2 : ({l1, l2} : Finset α).card = 2 := Finset.card_pair hpair_ne
    have hunion : ({l1, l2} ∪ s \ {l1, l2}) = s := by
      rw [Finset.union_comm]
      exact Finset.sdiff_union_of_subset hsub
    have hdisj : Disjoint ({l1, l2} : Finset α) (s \ {l1, l2}) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp hx2).2 hx1
    have hsum_split : ∑ y ∈ ({l1, l2} ∪ s \ {l1, l2}), g y =
      (∑ x ∈ ({l1, l2} : Finset α), g x) + ∑ x ∈ s \ {l1, l2}, g x :=
      Finset.sum_union hdisj
    rw [hunion] at hsum_split
    have hpair_sum : ∑ x ∈ ({l1, l2} : Finset α), g x = g l1 + g l2 :=
      Finset.sum_pair hpair_ne
    have hrest_ge : (s \ {l1, l2}).card ≤ ∑ x ∈ s \ {l1, l2}, g x := by
      have hle := Finset.sum_le_sum (s := s \ {l1, l2}) (f := fun _ => 1) (g := g)
        (fun i hi => hge i (Finset.mem_sdiff.mp hi).1)
      rwa [Finset.sum_const, nsmul_eq_mul, mul_one] at hle
    have hrest_card : (s \ {l1, l2}).card = s.card - 2 := by
      have hcu := Finset.card_union_of_disjoint hdisj
      rw [hunion, h2] at hcu
      omega
    omega
  have hg02 : g l0 = 2 := by
    by_contra hne
    have h3 : 3 ≤ g l0 := by omega
    have herase_card : (s.erase l0).card = s.card - 1 :=
      Finset.card_erase_of_mem hl0
    have hsplit : ∑ y ∈ s, g y = g l0 + ∑ y ∈ s.erase l0, g y :=
      (Finset.add_sum_erase s g hl0).symm
    have hrest : (s.erase l0).card ≤ ∑ y ∈ s.erase l0, g y := by
      have hle := Finset.sum_le_sum (s := s.erase l0) (f := fun _ => 1) (g := g)
        (fun i hi => hge i (Finset.mem_of_mem_erase hi))
      rwa [Finset.sum_const, nsmul_eq_mul, mul_one] at hle
    have hpos : 1 ≤ s.card := Finset.one_le_card.mpr ⟨l0, hl0⟩
    omega
  refine ⟨l0, hl0, hg02, ?_⟩
  intro l hl hne
  by_contra h1
  have h2l : 2 ≤ g l := by
    have hgl := hge l hl
    omega
  have heq := huniq l hl l0 hl0 h2l hg0
  exact hne heq

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLooseRepeat_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLooseRepeat_top {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
  (him : (knImg σ L).card = (knTop σ).card) :
  1 ≤ (knTop σ).card ∧ knImg σ L = knTop σ := by
  classical
  obtain ⟨hhappy, _⟩ := h
  obtain ⟨⟨hne, _, _⟩, hsub⟩ := hhappy
  obtain ⟨x, hx⟩ := hne
  have h1 : 1 ≤ (knImg σ L).card := by
    apply Finset.one_le_card.mpr
    exact ⟨L x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  constructor
  · omega
  · exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLooseRepeat_pair](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLooseRepeat_pair {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
  (himTop : knImg σ L = knTop σ) :
  ∃ w1 ∈ σ, ∃ w2 ∈ σ, w1 ≠ w2 ∧ L w1 = L w2 ∧
    (∀ a ∈ σ, ∀ b ∈ σ, L a = L b →
      a = b ∨ (a = w1 ∧ b = w2) ∨ (a = w2 ∧ b = w1)) := by
  classical
  obtain ⟨⟨_, _⟩, hcard⟩ := h
  have hfib_sum : ∑ ℓ ∈ knImg σ L, (σ.filter (fun x => L x = ℓ)).card =
    (knImg σ L).card + 1 := by
    have hfib := Finset.card_eq_sum_card_fiberwise (s := σ) (t := knImg σ L) (f := L)
      (fun x hx => Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨x, Finset.mem_coe.mp hx, rfl⟩))
    have him : (knImg σ L).card = (knTop σ).card := by
      rw [himTop]
    omega
  have hge : ∀ ℓ ∈ knImg σ L, 1 ≤ (σ.filter (fun x => L x = ℓ)).card := by
    intro ℓ hℓ
    have hmem : ℓ ∈ σ.image L := hℓ
    obtain ⟨x, hx, hxl⟩ := Finset.mem_image.mp hmem
    have hfibmem : x ∈ σ.filter (fun x => L x = ℓ) :=
      Finset.mem_filter.mpr ⟨hx, hxl⟩
    exact Finset.one_le_card.mpr ⟨x, hfibmem⟩
  obtain ⟨l0, hl0, hl02, hl1⟩ := knSum_two _ _ hge hfib_sum
  obtain ⟨w1, w2, hne, hfibeq⟩ := Finset.card_eq_two.mp hl02
  have hw1 : w1 ∈ σ ∧ L w1 = l0 := by
    have hself : w1 ∈ ({w1, w2} : Finset (Finset (Bool × Fin n))) :=
      Finset.mem_insert_self w1 {w2}
    rw [← hfibeq] at hself
    exact ⟨(Finset.mem_filter.mp hself).1, (Finset.mem_filter.mp hself).2⟩
  have hw2 : w2 ∈ σ ∧ L w2 = l0 := by
    have hself : w2 ∈ ({w1, w2} : Finset (Finset (Bool × Fin n))) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self w2)
    rw [← hfibeq] at hself
    exact ⟨(Finset.mem_filter.mp hself).1, (Finset.mem_filter.mp hself).2⟩
  refine ⟨w1, hw1.1, w2, hw2.1, hne, ?_, ?_⟩
  · rw [hw1.2, hw2.2]
  · intro a ha b hb hab
    have hl : L a ∈ knImg σ L := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    by_cases heq : L a = l0
    · have ha' : a ∈ ({w1, w2} : Finset (Finset (Bool × Fin n))) := by
      rw [← hfibeq]
      exact Finset.mem_filter.mpr ⟨ha, heq⟩
      have hb' : b ∈ ({w1, w2} : Finset (Finset (Bool × Fin n))) := by
        rw [← hfibeq]
        exact Finset.mem_filter.mpr ⟨hb, by rw [← hab]; exact heq⟩
      rw [Finset.mem_insert, Finset.mem_singleton] at ha' hb'
      obtain rfl | rfl <;> rcases hb' with rfl | rfl := ha'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inl rfl
    · have h1 := hl1 (L a) hl heq
      have ha' : a ∈ σ.filter (fun x => L x = L a) :=
        Finset.mem_filter.mpr ⟨ha, rfl⟩
      have hb' : b ∈ σ.filter (fun x => L x = L a) :=
        Finset.mem_filter.mpr ⟨hb, hab.symm⟩
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h1
      rw [hc] at ha' hb'
      have hac : a = c := Finset.mem_singleton.mp ha'
      have hbc : b = c := Finset.mem_singleton.mp hb'
      exact Or.inl (hac.trans hbc.symm)

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLooseRepeat_no_out](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLooseRepeat_no_out {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
  (himTop : knImg σ L = knTop σ) : knOut σ L = ∅ := by
  classical
  have hchain : knChain σ := h.1.1
  ext v
  simp only [knMem_out, Finset.notMem_empty, iff_false]
  intro hv
  obtain ⟨hvn, hchainI, htopI⟩ := hv
  have htopmem : knTop σ ∈ σ := knChain_top_mem σ hchain
  obtain ⟨_, _, hischI⟩ := hchainI
  have hvt : v ⊆ knTop σ ∨ knTop σ ⊆ v := by
    have h1 : v ∈ insert v σ := Finset.mem_insert_self v σ
    have h2 : knTop σ ∈ insert v σ := Finset.mem_insert_of_mem htopmem
    obtain hsub | hsub := hischI v h1 (knTop σ) h2
    · exact Or.inl hsub
    · exact Or.inr hsub
  obtain hsub | hsup := hvt
  · have hle : v.card ≤ (knTop σ).card := Finset.card_le_card hsub
    obtain ⟨x, hx, hxc⟩ := knLoose_has_level σ L h hle
    have hxv : x ∈ insert v σ := Finset.mem_insert_of_mem hx
    have hvv : v ∈ insert v σ := Finset.mem_insert_self v σ
    have heq : x = v := knChain_eq_of_mem_card_eq _ hischI hxv hvv hxc
    rw [heq] at hx
    exact hvn hx
  · have htopI' : knTop (insert v σ) ⊆ knTop σ := by
    rwa [himTop] at htopI
    have hvinsert : knTop (insert v σ) = v := knTop_insert_of_supset σ v hsup
    rw [hvinsert] at htopI'
    have heq : v = knTop σ := le_antisymm htopI' hsup
    rw [heq] at hvn
    exact hvn htopmem

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLooseRepeat_in_of_pair](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLooseRepeat_in_of_pair {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
  (himTop : knImg σ L = knTop σ)
  (w w' : Finset (Bool × Fin n)) (hw : w ∈ σ) (hw' : w' ∈ σ)
  (hne : w' ≠ w) (heq : L w = L w') : w ∈ knIn σ L := by
  classical
  have hchain : knChain σ := h.1.1
  have hcons : ∀ x ∈ σ, knConsistent x := hchain.2.1
  have hisch : knIsChain σ := hchain.2.2
  have himg_erase : knImg (σ.erase w) L = knTop σ := by
    apply le_antisymm
    · calc knImg (σ.erase w) L ⊆ knImg σ L :=
      Finset.image_subset_image (Finset.erase_subset w σ)
      _ = knTop σ := himTop
    · rw [← himTop]
      intro ℓ hℓ
      obtain ⟨x, hx, hxl⟩ := Finset.mem_image.mp hℓ
      by_cases hxw : x = w
      · have hlw' : L w' = ℓ := by
        rwa [← hxl, hxw]
        have hwe : w' ∈ σ.erase w := Finset.mem_erase.mpr ⟨hne, hw'⟩
        exact Finset.mem_image.mpr ⟨w', hwe, hlw'⟩
      · have hxe : x ∈ σ.erase w := Finset.mem_erase.mpr ⟨hxw, hx⟩
        exact Finset.mem_image.mpr ⟨x, hxe, hxl⟩
  have hchainE : knChain (σ.erase w) := by
    refine ⟨⟨w', Finset.mem_erase.mpr ⟨hne, hw'⟩⟩, ?_, ?_⟩
    · intro x hx
      exact hcons x (Finset.mem_of_mem_erase hx)
    · intro a ha b hb
      exact hisch a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
  have hhappy : knHappy (σ.erase w) L := by
    refine ⟨hchainE, ?_⟩
    rw [himg_erase]
    exact knTop_sup_le _ (fun x hx => knMem_subset_top σ (Finset.mem_of_mem_erase hx))
  rw [knMem_in]
  refine ⟨hw, hhappy, ?_⟩
  rw [himg_erase]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLooseRepeat_in](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLooseRepeat_in {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
  (himTop : knImg σ L = knTop σ)
  (w1 w2 : Finset (Bool × Fin n)) (hw1 : w1 ∈ σ) (hw2 : w2 ∈ σ)
  (hne : w1 ≠ w2) (heq12 : L w1 = L w2)
  (huniq : ∀ a ∈ σ, ∀ b ∈ σ, L a = L b →
    a = b ∨ (a = w1 ∧ b = w2) ∨ (a = w2 ∧ b = w1)) :
  knIn σ L = {w1, w2} := by
  classical
  ext w
  rw [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hw
    rw [knMem_in] at hw
    obtain ⟨hwm, _, htopsub⟩ := hw
    by_contra hcon
    have hw1' : w ≠ w1 := fun he => hcon (Or.inl he)
    have hw2' : w ≠ w2 := fun he => hcon (Or.inr he)
    have hnot : L w ∉ knImg (σ.erase w) L := by
      intro hmem
      obtain ⟨x, hx, hxl⟩ := Finset.mem_image.mp hmem
      have hxσ : x ∈ σ := Finset.mem_of_mem_erase hx
      have hxw : x ≠ w := (Finset.mem_erase.mp hx).1
      have hxl' : L x = L w := hxl
      obtain heq | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := huniq x hxσ w hwm hxl'
      · exact hxw heq
      · exact hw2' rfl
      · exact hw1' rfl
    have hmem2 : L w ∈ knImg (σ.erase w) L := by
      have htopw : L w ∈ knTop σ := by
        rw [← himTop]
        exact Finset.mem_image.mpr ⟨w, hwm, rfl⟩
      exact htopsub htopw
    exact hnot hmem2
  · intro hw
    obtain heqw | heqw := hw
    · rw [heqw]
      exact knLooseRepeat_in_of_pair σ L h himTop w1 w2 hw1 hw2 (Ne.symm hne)
        heq12
    · rw [heqw]
      exact knLooseRepeat_in_of_pair σ L h himTop w2 w1 hw2 hw1 hne
        heq12.symm

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLooseRepeat_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLooseRepeat_degree {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
  (him : (knImg σ L).card = (knTop σ).card) : (knG L).degree σ = 2 := by
  classical
  obtain ⟨_, himTop⟩ := knLooseRepeat_top σ L h him
  obtain ⟨w1, hw1, w2, hw2, hne, heq12, huniq⟩ :=
    knLooseRepeat_pair σ L h himTop
  have hout : (knOut σ L).card = 0 := by
    rw [knLooseRepeat_no_out σ L h himTop, Finset.card_empty]
  have hin : (knIn σ L).card = 2 := by
    rw [knLooseRepeat_in σ L h himTop w1 w2 hw1 hw2 hne heq12 huniq,
      Finset.card_pair hne]
  have hdeg := knDegree_eq σ L h.1
  omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLooseFresh_inj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLooseFresh_inj {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
  (him : (knImg σ L).card = (knTop σ).card + 1) :
  Set.InjOn L (↑σ : Set (Finset (Bool × Fin n))) := by
  classical
  obtain ⟨_, hcard⟩ := h
  have h2 : (σ.image L).card = σ.card := by
    have hcc : (knImg σ L).card = σ.card := by omega
    unfold knImg at hcc
    exact hcc
  exact Finset.injOn_of_card_image_eq h2

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLooseFresh_label](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLooseFresh_label {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
  (him : (knImg σ L).card = (knTop σ).card + 1) :
  ∃ ℓ, ℓ ∉ knTop σ ∧ ℓ ∈ knImg σ L ∧ knImg σ L = insert ℓ (knTop σ) := by
  classical
  have hsub : knTop σ ⊆ knImg σ L := h.1.2
  have hsd : (knImg σ L \ knTop σ).card = 1 := by
    have hunion := Finset.sdiff_union_of_subset hsub
    have hdisj : Disjoint (knImg σ L \ knTop σ) (knTop σ) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp hx1).2 hx2
    have hcu := Finset.card_union_of_disjoint hdisj
    rw [hunion] at hcu
    omega
  obtain ⟨ℓ, hℓ⟩ := Finset.card_eq_one.mp hsd
  have hℓtop : ℓ ∉ knTop σ := by
    have hself : ℓ ∈ ({ℓ} : Finset (Bool × Fin n)) := Finset.mem_singleton_self ℓ
    rw [← hℓ] at hself
    exact (Finset.mem_sdiff.mp hself).2
  have hℓimg : ℓ ∈ knImg σ L := by
    have hself : ℓ ∈ ({ℓ} : Finset (Bool × Fin n)) := Finset.mem_singleton_self ℓ
    rw [← hℓ] at hself
    exact (Finset.mem_sdiff.mp hself).1
  refine ⟨ℓ, hℓtop, hℓimg, ?_⟩
  ext m
  rw [Finset.mem_insert]
  constructor
  · intro hm
    by_cases hmt : m ∈ knTop σ
    · exact Or.inr hmt
    · left
      have hmem : m ∈ knImg σ L \ knTop σ := Finset.mem_sdiff.mpr ⟨hm, hmt⟩
      rw [hℓ] at hmem
      exact Finset.mem_singleton.mp hmem
  · intro hm
    obtain rfl | hm := hm
    · exact hℓimg
    · exact hsub hm

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knFresh_neg_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knFresh_neg_top {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
  (hnc : knNoCompl L)
  (w : Finset (Bool × Fin n)) (hwσ : w ∈ σ)
  (ℓ : Bool × Fin n) (hwl : L w = ℓ) :
  knNegLabel ℓ ∉ knTop σ := by
  classical
  have hchain : knChain σ := h.1.1
  have hcons : ∀ x ∈ σ, knConsistent x := hchain.2.1
  have hisch : knIsChain σ := hchain.2.2
  have hsub : knTop σ ⊆ knImg σ L := h.1.2
  intro hmem
  have hmem2 : knNegLabel ℓ ∈ knImg σ L := hsub hmem
  obtain ⟨x, hx, hxl⟩ := Finset.mem_image.mp hmem2
  have hcomp := hisch x hx w hwσ
  have hxlw : L x = knNegLabel (L w) := by
    rwa [hwl]
  obtain hsub2 | hsub2 := hcomp
  · have hncx := hnc x w (hcons x hx) (hcons w hwσ) hsub2
    apply hncx
    rw [hxlw, knNegLabel_invol_apply]
  · have hncx := hnc w x (hcons w hwσ) (hcons x hx) hsub2
    exact hncx hxlw

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knFresh_insert_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knFresh_insert_cons {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
  (hnc : knNoCompl L)
  (w : Finset (Bool × Fin n)) (hwσ : w ∈ σ)
  (ℓ : Bool × Fin n) (hwl : L w = ℓ) (hℓtop : ℓ ∉ knTop σ) :
  knConsistent (insert ℓ (knTop σ)) := by
  classical
  have hchain : knChain σ := h.1.1
  have htopmem : knTop σ ∈ σ := knChain_top_mem σ hchain
  have hconTop : knConsistent (knTop σ) := hchain.2.1 _ htopmem
  have hnegtop : knNegLabel ℓ ∉ knTop σ :=
    knFresh_neg_top σ L h hnc w hwσ ℓ hwl
  intro l hl hnl
  rw [Finset.mem_insert] at hl hnl
  obtain heq | hl := hl
  · rw [heq] at hnl
    obtain hnl | hnl := hnl
    · have hne2 : knNegLabel ℓ ≠ ℓ := by
      obtain ⟨b, i⟩ := ℓ
      cases b <;> simp [knNegLabel]
      exact hne2 hnl
    · exact hnegtop hnl
  · rcases hnl with hnl | hnl
    · have h2 : knNegLabel ℓ = l := by
      rw [← hnl, knNegLabel_invol_apply]
      rw [h2] at hnegtop
      exact hnegtop hl
    · exact hconTop l hl hnl

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLooseFresh_out](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLooseFresh_out {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
  (hnc : knNoCompl L)
  (w : Finset (Bool × Fin n)) (hwσ : w ∈ σ)
  (ℓ : Bool × Fin n) (hwl : L w = ℓ) (hℓtop : ℓ ∉ knTop σ)
  (hfresh : knImg σ L = insert ℓ (knTop σ)) :
  knOut σ L = {insert ℓ (knTop σ)} := by
  classical
  have hchain : knChain σ := h.1.1
  have hconsI : knConsistent (insert ℓ (knTop σ)) :=
    knFresh_insert_cons σ L h hnc w hwσ ℓ hwl hℓtop
  have htopmem : knTop σ ∈ σ := knChain_top_mem σ hchain
  ext v
  rw [Finset.mem_singleton]
  constructor
  · intro hv
    rw [knMem_out] at hv
    obtain ⟨hvn, hchainI, htopI⟩ := hv
    obtain ⟨_, _, hischI⟩ := hchainI
    have hsup : knTop σ ⊆ v := by
      have hcomp := hischI v (Finset.mem_insert_self v σ) (knTop σ)
        (Finset.mem_insert_of_mem htopmem)
      obtain hsub | hsup := hcomp
      · exfalso
        have hle : v.card ≤ (knTop σ).card := Finset.card_le_card hsub
        obtain ⟨x, hx, hxc⟩ := knLoose_has_level σ L h hle
        have hxv : x ∈ insert v σ := Finset.mem_insert_of_mem hx
        have hvv : v ∈ insert v σ := Finset.mem_insert_self v σ
        have heq : x = v := knChain_eq_of_mem_card_eq _ hischI hxv hvv hxc
        rw [heq] at hx
        exact hvn hx
      · exact hsup
    have hvinsert : knTop (insert v σ) = v := knTop_insert_of_supset σ v hsup
    rw [hvinsert, hfresh] at htopI
    have hsubI : insert ℓ (knTop σ) ⊆ v := by
      have hssub : knTop σ ⊂ v := by
        refine ⟨hsup, ?_⟩
        intro hsub
        have hle : v.card ≤ (knTop σ).card := Finset.card_le_card hsub
        obtain ⟨x, hx, hxc⟩ := knLoose_has_level σ L h hle
        have hxv : x ∈ insert v σ := Finset.mem_insert_of_mem hx
        have hvv : v ∈ insert v σ := Finset.mem_insert_self v σ
        have heq : x = v := knChain_eq_of_mem_card_eq _ hischI hxv hvv hxc
        rw [heq] at hx
        exact hvn hx
      obtain ⟨y, hyv, hytop⟩ := Finset.exists_of_ssubset hssub
      have hyI : y ∈ insert ℓ (knTop σ) := htopI hyv
      rw [Finset.mem_insert] at hyI
      obtain rfl | hyI := hyI
      · exact Finset.insert_subset hyv hsup
      · exact absurd hyI hytop
    exact le_antisymm htopI hsubI
  · intro heq
    rw [heq]
    have hcardI : (insert ℓ (knTop σ)).card = (knTop σ).card + 1 :=
      Finset.card_insert_of_notMem hℓtop
    have hnem : insert ℓ (knTop σ) ∉ σ := by
      intro hcon
      have hle := Finset.card_le_card (knMem_subset_top σ hcon)
      omega
    have hcompI : ∀ x ∈ σ, x ⊆ insert ℓ (knTop σ) ∨ insert ℓ (knTop σ) ⊆ x := by
      intro x hx
      exact Or.inl ((knMem_subset_top σ hx).trans (Finset.subset_insert ℓ _))
    have hchainI := knChain_insert σ hchain hconsI hcompI
    rw [knMem_out]
    refine ⟨hnem, hchainI, ?_⟩
    have htopI2 : knTop (insert (insert ℓ (knTop σ)) σ) = insert ℓ (knTop σ) := by
      apply knTop_insert_of_supset
      exact Finset.subset_insert ℓ _
    rw [htopI2, hfresh]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLooseFresh_in_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLooseFresh_in_sub {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
  (w : Finset (Bool × Fin n)) (hw : w ∈ σ)
  (ℓ : Bool × Fin n) (hwl : L w = ℓ) (hℓtop : ℓ ∉ knTop σ)
  {u : Finset (Bool × Fin n)} (hu : u ∈ knIn σ L) : u = w := by
  classical
  have hcard : σ.card = (knTop σ).card + 1 := h.2
  rw [knMem_in] at hu
  obtain ⟨hum, _, htopsub⟩ := hu
  have himg_eq : knImg (σ.erase u) L = knTop σ := by
    have hle : (knImg (σ.erase u) L).card ≤ (knTop σ).card := by
      calc (knImg (σ.erase u) L).card ≤ (σ.erase u).card := by
        unfold knImg
        exact Finset.card_image_le
        _ = σ.card - 1 := Finset.card_erase_of_mem hum
        _ = (knTop σ).card := by omega
    exact (Finset.eq_of_subset_of_card_le htopsub hle).symm
  by_contra hne2
  have hwu : w ∈ σ.erase u := Finset.mem_erase.mpr ⟨Ne.symm hne2, hw⟩
  have hmem : L w ∈ knImg (σ.erase u) L := Finset.mem_image.mpr ⟨w, hwu, rfl⟩
  rw [himg_eq, hwl] at hmem
  exact hℓtop hmem

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLooseFresh_mem_in](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLooseFresh_mem_in {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
  (hinj : Set.InjOn L (↑σ : Set (Finset (Bool × Fin n))))
  (w : Finset (Bool × Fin n)) (hw : w ∈ σ)
  (ℓ : Bool × Fin n) (hwl : L w = ℓ) (hℓtop : ℓ ∉ knTop σ)
  (hfresh : knImg σ L = insert ℓ (knTop σ)) :
  w ∈ knIn σ L ↔ (σ.erase w).Nonempty := by
  classical
  have hchain : knChain σ := h.1.1
  have hcons : ∀ x ∈ σ, knConsistent x := hchain.2.1
  have hisch : knIsChain σ := hchain.2.2
  have hsub : knTop σ ⊆ knImg σ L := h.1.2
  have himg_erase : knImg (σ.erase w) L = knTop σ := by
    apply le_antisymm
    · intro m hm
      obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hm
      have hxσ : x ∈ σ := Finset.mem_of_mem_erase hx
      have hxw : x ≠ w := (Finset.mem_erase.mp hx).1
      have hmemI : L x ∈ knImg σ L := Finset.mem_image.mpr ⟨x, hxσ, rfl⟩
      rw [hfresh] at hmemI
      obtain heq | htop := Finset.mem_insert.mp hmemI
      · exfalso
        have hxx : L x = L w := heq.trans hwl.symm
        have hxeq : x = w :=
          hinj (Finset.mem_coe.mpr hxσ) (Finset.mem_coe.mpr hw) hxx
        exact hxw hxeq
      · rw [← hxm]
        exact htop
    · intro m hm
      have hmemI : m ∈ knImg σ L := hsub hm
      obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hmemI
      by_cases hxw : x = w
      · exfalso
        subst hxw
        rw [hwl] at hxm
        rw [hxm] at hℓtop
        exact hℓtop hm
      · have hxe : x ∈ σ.erase w := Finset.mem_erase.mpr ⟨hxw, hx⟩
        exact Finset.mem_image.mpr ⟨x, hxe, hxm⟩
  constructor
  · intro hwIn
    rw [knMem_in] at hwIn
    obtain ⟨_, hhappy, _⟩ := hwIn
    exact hhappy.1.1
  · intro hne2
    have hchainE : knChain (σ.erase w) := by
      obtain ⟨w', hw'⟩ := hne2
      refine ⟨⟨w', hw'⟩, ?_, ?_⟩
      · intro x hx
        exact hcons x (Finset.mem_of_mem_erase hx)
      · intro a ha b hb
        exact hisch a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
    have hhappy : knHappy (σ.erase w) L := by
      refine ⟨hchainE, ?_⟩
      rw [himg_erase]
      exact knTop_sup_le _ (fun x hx => knMem_subset_top σ (Finset.mem_of_mem_erase hx))
    rw [knMem_in]
    refine ⟨hw, hhappy, ?_⟩
    rw [himg_erase]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLooseFresh_erase_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLooseFresh_erase_empty {n : ℕ}
  (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
  (w : Finset (Bool × Fin n)) (hw : w ∈ σ) :
  (σ.erase w = ∅) ↔ σ = {∅} := by
  classical
  constructor
  · intro herase
    have hsub1 : σ ⊆ {w} := by
      intro x hx
      rw [Finset.mem_singleton]
      by_contra hne
      have hmem : x ∈ σ.erase w := Finset.mem_erase.mpr ⟨hne, hx⟩
      rw [herase] at hmem
      exact Finset.notMem_empty x hmem
    have hsingle : σ = {w} := by
      apply le_antisymm hsub1
      intro x hx
      rw [Finset.mem_singleton] at hx
      rwa [hx]
    have hcard1 : σ.card = 1 := by
      rw [hsingle, Finset.card_singleton]
    have hcard := h.2
    have htop0 : knTop σ = ∅ := by
      have hzero : (knTop σ).card = 0 := by omega
      exact Finset.card_eq_zero.mp hzero
    have hw0 : w = ∅ := by
      have hsubw : w ⊆ knTop σ := knMem_subset_top σ hw
      rw [htop0] at hsubw
      have hle : w.card ≤ (∅ : Finset (Bool × Fin n)).card :=
        Finset.card_le_card hsubw
      rw [Finset.card_empty] at hle
      have hzero : w.card = 0 := by omega
      exact Finset.card_eq_zero.mp hzero
    rw [hsingle, hw0]
  · intro hσ
    have hw0 : w = ∅ := Finset.mem_singleton.mp (by rw [← hσ]; exact hw)
    rw [hσ, hw0, Finset.erase_singleton]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLooseFresh_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLooseFresh_degree {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
  (him : (knImg σ L).card = (knTop σ).card + 1) (hnc : knNoCompl L) :
  ((knG L).degree σ = 1 ∧ σ = {∅}) ∨ ((knG L).degree σ = 2 ∧ σ ≠ {∅}) := by
  classical
  have hinj := knLooseFresh_inj σ L h him
  obtain ⟨ℓ, hℓtop, hℓimg, hfresh⟩ := knLooseFresh_label σ L h him
  obtain ⟨w, hwσ, hwl⟩ := Finset.mem_image.mp hℓimg
  have hout : (knOut σ L).card = 1 := by
    rw [knLooseFresh_out σ L h hnc w hwσ ℓ hwl hℓtop hfresh,
      Finset.card_singleton]
  by_cases herase : σ.erase w = ∅
  · left
    have hin0 : (knIn σ L).card = 0 := by
      have hin_empty : knIn σ L = ∅ := by
        ext u
        simp only [Finset.notMem_empty, iff_false]
        intro hu
        have huw : u = w := knLooseFresh_in_sub σ L h w hwσ ℓ hwl hℓtop hu
        rw [knMem_in] at hu
        obtain ⟨_, hhappy, _⟩ := hu
        have hne2 := hhappy.1.1
        rw [huw, herase] at hne2
        exact Finset.not_nonempty_empty hne2
      rw [hin_empty, Finset.card_empty]
    rw [knDegree_eq σ L h.1, hout, hin0, add_zero]
    refine ⟨rfl, ?_⟩
    exact (knLooseFresh_erase_empty σ L h w hwσ).mp herase
  · right
    have hmem : w ∈ knIn σ L :=
      (knLooseFresh_mem_in σ L h hinj w hwσ ℓ hwl hℓtop hfresh).mpr
        (Finset.nonempty_iff_ne_empty.mpr herase)
    have hin1 : (knIn σ L).card = 1 := by
      have hsingle : knIn σ L = {w} := by
        ext u
        rw [Finset.mem_singleton]
        constructor
        · intro hu
          exact knLooseFresh_in_sub σ L h w hwσ ℓ hwl hℓtop hu
        · intro hu
          rwa [hu]
      rw [hsingle, Finset.card_singleton]
    rw [knDegree_eq σ L h.1, hout, hin1]
    refine ⟨rfl, ?_⟩
    intro hcon
    have herase' := (knLooseFresh_erase_empty σ L h w hwσ).mpr hcon
    exact herase herase'

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTop_singleton_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTop_singleton_empty {n : ℕ} :
  knTop ({∅} : Finset (Finset (Bool × Fin n))) = ∅ := by
  classical
  have hsup : (({∅} : Finset (Finset (Bool × Fin n))).sup id) = id ∅ :=
    Finset.sup_singleton
  have hid : id (∅ : Finset (Bool × Fin n)) = ∅ := rfl
  unfold knTop
  rw [hsup, hid]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knEmptySingleton_chain](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knEmptySingleton_chain {n : ℕ} :
  knChain ({∅} : Finset (Finset (Bool × Fin n))) := by
  classical
  refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    intro l hl
    exact False.elim (Finset.notMem_empty l hl)
  · intro a ha b hb
    rw [Finset.mem_singleton] at ha hb
    rw [ha, hb]
    exact Or.inl Subset.rfl

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knEmptySingleton_happy](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knEmptySingleton_happy {n : ℕ}
  (L : Finset (Bool × Fin n) → Bool × Fin n) :
  knHappy ({∅} : Finset (Finset (Bool × Fin n))) L := by
  classical
  refine ⟨knEmptySingleton_chain, ?_⟩
  rw [knTop_singleton_empty]
  exact Finset.empty_subset _

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knEmptySingleton_loose](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knEmptySingleton_loose {n : ℕ}
  (L : Finset (Bool × Fin n) → Bool × Fin n) :
  knLoose ({∅} : Finset (Finset (Bool × Fin n))) L := by
  classical
  refine ⟨knEmptySingleton_happy L, ?_⟩
  have h1 : ({∅} : Finset (Finset (Bool × Fin n))).card = 1 :=
    Finset.card_singleton _
  have h0 : (knTop ({∅} : Finset (Finset (Bool × Fin n)))).card = 0 := by
    rw [knTop_singleton_empty, Finset.card_empty]
  omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knOddDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knOddDegree {n : ℕ}
  (L : Finset (Bool × Fin n) → Bool × Fin n) (hnc : knNoCompl L)
  (σ : Finset (Finset (Bool × Fin n))) :
  Odd ((knG L).degree σ) ↔ σ = {∅} ∨ (knTight σ L ∧ ∅ ∉ σ) := by
  classical
  by_cases hhappy : knHappy σ L
  · obtain hcard_eq := knHappy_card_eq σ L hhappy
    obtain htight_card | hloose_card := hcard_eq
    · have htight : knTight σ L := ⟨hhappy, htight_card⟩
      have hdeg := knTight_degree σ L htight
      have hnotsingle : σ ≠ {∅} := by
        intro hcon
        rw [hcon, Finset.card_singleton, knTop_singleton_empty,
          Finset.card_empty] at htight_card
        omega
      constructor
      · intro hodd
        right
        refine ⟨htight, ?_⟩
        obtain ⟨h1, hnem⟩ | ⟨h2, _⟩ := hdeg
        · exact hnem
        · exfalso
          rw [h2] at hodd
          exact (by decide : ¬ Odd 2) hodd
      · intro hdisj
        obtain hsingle | ⟨_, hnem⟩ := hdisj
        · exact absurd hsingle hnotsingle
        · rcases hdeg with ⟨h1, _⟩ | ⟨_, hmem⟩
          · rw [h1]
            exact odd_one
          · exact absurd hmem hnem
    · have hloose : knLoose σ L := ⟨hhappy, hloose_card⟩
      have him_le : (knImg σ L).card ≤ σ.card := by
        unfold knImg
        exact Finset.card_image_le
      have htop_le : (knTop σ).card ≤ (knImg σ L).card :=
        Finset.card_le_card hhappy.2
      by_cases him_eq : (knImg σ L).card = (knTop σ).card
      · have hdeg2 := knLooseRepeat_degree σ L hloose him_eq
        have hnotsingle : σ ≠ {∅} := by
          intro hcon
          rw [hcon] at him_eq
          rw [knTop_singleton_empty, Finset.card_empty] at him_eq
          have himg1 : (knImg ({∅} : Finset (Finset (Bool × Fin n))) L).card = 1 := by
            unfold knImg
            rw [Finset.image_singleton, Finset.card_singleton]
          omega
        constructor
        · intro hodd
          rw [hdeg2] at hodd
          exact absurd hodd (by decide : ¬ Odd 2)
        · intro hdisj
          obtain hsingle | ⟨htight2, _⟩ := hdisj
          · exact absurd hsingle hnotsingle
          · obtain ⟨_, htcard⟩ := htight2
            omega
      · have him2 : (knImg σ L).card = (knTop σ).card + 1 := by omega
        have hdeg := knLooseFresh_degree σ L hloose him2 hnc
        constructor
        · intro hodd
          obtain ⟨h1, hsingle⟩ | ⟨h2, _⟩ := hdeg
          · exact Or.inl hsingle
          · exfalso
            rw [h2] at hodd
            exact absurd hodd (by decide : ¬ Odd 2)
        · intro hdisj
          obtain hsingle | ⟨htight2, hnem⟩ := hdisj
          · rcases hdeg with ⟨h1, _⟩ | ⟨_, hne2⟩
            · rw [h1]
              exact odd_one
            · exact absurd hsingle hne2
          · obtain ⟨_, htcard⟩ := htight2
            omega
  · have hdeg0 := knDegree_nothappy σ L hhappy
    have hnotsingle : σ ≠ {∅} := by
      intro hcon
      rw [hcon] at hhappy
      exact hhappy (knEmptySingleton_happy L)
    constructor
    · intro hodd
      rw [hdeg0] at hodd
      exact absurd hodd (by decide : ¬ Odd (0 : ℕ))
    · intro hdisj
      obtain hsingle | ⟨htight2, _⟩ := hdisj
      · exact absurd hsingle hnotsingle
      · exact absurd htight2.1 hhappy

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNegLabel_snd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNegLabel_snd {n : ℕ} (m : Bool × Fin n) :
  (knNegLabel m).2 = m.2 :=
  rfl

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNegCell_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNegCell_injective {n : ℕ} :
  Function.Injective (@knNegCell n) :=
  Function.Involutive.injective (fun x => knNegCell_invol x)

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNegCell_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNegCell_mono {n : ℕ} {x y : Finset (Bool × Fin n)}
  (h : x ⊆ y) : knNegCell x ⊆ knNegCell y := by
  classical
  intro l hl
  obtain ⟨m, hm, hml⟩ := knMem_negCell.mp hl
  rw [← hml]
  exact knNegLabel_mem_negCell (h hm)

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNegTop](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNegTop {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (h : knChain σ) :
  knTop (σ.image knNegCell) = knNegCell (knTop σ) := by
  classical
  apply le_antisymm
  · apply knTop_sup_le
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    rw [← hxy]
    exact knNegCell_mono (knMem_subset_top σ hx)
  · have hmem : knNegCell (knTop σ) ∈ σ.image knNegCell :=
    Finset.mem_image.mpr ⟨knTop σ, knChain_top_mem σ h, rfl⟩
    exact knMem_subset_top _ hmem

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNegImage_invol](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNegImage_invol {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) :
  (σ.image knNegCell).image knNegCell = σ := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, hyz⟩ := Finset.mem_image.mp hy
    have h2 : knNegCell y = z := by
      rw [← hyz]
      exact knNegCell_invol z
    rwa [← hxy, h2]
  · intro hx
    exact Finset.mem_image.mpr
      ⟨knNegCell x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, knNegCell_invol x⟩

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knMem_tightSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knMem_tightSet {n : ℕ} {σ : Finset (Finset (Bool × Fin n))}
  {L : Finset (Bool × Fin n) → Bool × Fin n} :
  σ ∈ knTightSet L ↔ knTight σ L ∧ ∅ ∉ σ := by
  classical
  unfold knTightSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knPosMin_flip](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knPosMin_flip {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
  (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) :
  knPosMin σ ↔ ¬ knPosMin (σ.image knNegCell) := by
  classical
  have hchain : knChain σ := h.1.1
  have htopmem : knTop σ ∈ σ := knChain_top_mem σ hchain
  have hconTop : knConsistent (knTop σ) := hchain.2.1 _ htopmem
  have htopI : knTop (σ.image knNegCell) = knNegCell (knTop σ) :=
    knNegTop σ hchain
  have hI : (knTop (σ.image knNegCell)).image Prod.snd =
    (knTop σ).image Prod.snd := by
    rw [htopI]
    ext j
    constructor
    · intro hj
      obtain ⟨l, hl, hlj⟩ := Finset.mem_image.mp hj
      obtain ⟨m, hm, hml⟩ := knMem_negCell.mp hl
      have hmj : m.2 = j := by
        rw [← hlj, ← hml, knNegLabel_snd]
      exact Finset.mem_image.mpr ⟨m, hm, hmj⟩
    · intro hj
      obtain ⟨m, hm, hmj⟩ := Finset.mem_image.mp hj
      have hmem : knNegLabel m ∈ knNegCell (knTop σ) :=
        knNegLabel_mem_negCell hm
      have hmj2 : (knNegLabel m).2 = j := by
        rw [knNegLabel_snd, hmj]
      exact Finset.mem_image.mpr ⟨knNegLabel m, hmem, hmj2⟩
  have htopne : (knTop σ).Nonempty := by
    have hpos := knTight_top_card_pos σ L h
    exact Finset.card_pos.mp (by omega)
  constructor
  · intro hP hPf
    obtain ⟨i, hi, hmin⟩ := hP
    obtain ⟨i', hi', hmin'⟩ := hPf
    rw [htopI] at hi'
    obtain ⟨m, hm, hmi⟩ := knMem_negCell.mp hi'
    have hm1 : m.1 = false := by
      have h1 : (!m.1) = true := congrArg Prod.fst hmi
      cases hm1 : m.1 <;> simp_all
    have hm2 : m.2 = i' := congrArg Prod.snd hmi
    have hmeq : m = (false, i') := Prod.ext hm1 hm2
    rw [hmeq] at hm
    have hiI : i' ∈ (knTop σ).image Prod.snd :=
      Finset.mem_image.mpr ⟨(false, i'), hm, rfl⟩
    have hiIf : i ∈ (knTop (σ.image knNegCell)).image Prod.snd := by
      rw [hI]
      exact Finset.mem_image.mpr ⟨(true, i), hi, rfl⟩
    have heq : i' = i := le_antisymm (hmin' i hiIf) (hmin i' hiI)
    have hcon : knNegLabel (true, i') ∈ knTop σ := by
      have hneg : knNegLabel (true, i') = (false, i') := rfl
      rwa [hneg]
    rw [← heq] at hi
    exact hconTop _ hi hcon
  · intro hcon
    have hIne : ((knTop σ).image Prod.snd).Nonempty := by
      obtain ⟨l, hl⟩ := htopne
      exact ⟨l.2, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩
    have hisLeast := ((knTop σ).image Prod.snd).isLeast_min' hIne
    have hi0mem : Finset.min' ((knTop σ).image Prod.snd) hIne ∈
      (knTop σ).image Prod.snd := Finset.mem_coe.mp hisLeast.1
    have hi0le : ∀ j ∈ (knTop σ).image Prod.snd,
      Finset.min' ((knTop σ).image Prod.snd) hIne ≤ j := by
      intro j hj
      exact hisLeast.2 (Finset.mem_coe.mpr hj)
    obtain ⟨l, hl, hlj⟩ :=
      Finset.mem_image.mp hi0mem
    by_cases hlb : l.1 = true
    · refine ⟨l.2, ?_, ?_⟩
      · have hle : l = (true, l.2) := Prod.ext hlb rfl
        rwa [hle] at hl
      · intro j hj
        rw [hlj]
        exact hi0le j hj
    · have hlf : l.1 = false := by
      cases h : l.1 <;> simp_all
      exfalso
      apply hcon
      refine ⟨l.2, ?_, ?_⟩
      · have hll : l = (false, l.2) := Prod.ext hlf rfl
        rw [htopI, knMem_negCell]
        exact ⟨(false, l.2), by rw [← hll]; exact hl, rfl⟩
      · intro j hj
        rw [hI] at hj
        rw [hlj]
        exact hi0le j hj

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knPos_negCell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knPos_negCell {n : ℕ} (x : Finset (Bool × Fin n)) :
  knPos (knNegCell x) = knNegIdx x := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp hi
    have hl1 : l.1 = true := (Finset.mem_filter.mp hl).2
    obtain ⟨m, hm, hml⟩ := knMem_negCell.mp
      (Finset.mem_of_mem_filter _ hl)
    have hmb : m.1 = false := by
      have h1 := congrArg Prod.fst hml
      rw [hl1] at h1
      have hfst : (knNegLabel m).1 = (!m.1) := rfl
      rw [hfst] at h1
      cases hm1 : m.1 <;> simp_all
    have hmi : m.2 = i := by
      have := congrArg Prod.snd hml
      simp only [knNegLabel] at this
      omega
    have hmem : (false, i) ∈ x.filter (fun l => l.1 = false) := by
      rw [Finset.mem_filter]
      refine ⟨?_, rfl⟩
      rw [← hmi]
      have hme : m = (false, m.2) := Prod.ext hmb rfl
      rwa [hme] at hm
    have himg : i ∈ knNegIdx x :=
      Finset.mem_image.mpr ⟨(false, i), hmem, rfl⟩
    exact himg
  · intro hi
    obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp hi
    have hl1 : l.1 = false := (Finset.mem_filter.mp hl).2
    have hlm : l ∈ x := Finset.mem_of_mem_filter _ hl
    have hmem : knNegLabel l ∈ knNegCell x := knNegLabel_mem_negCell hlm
    have hmemf : knNegLabel l ∈
      (knNegCell x).filter (fun l => l.1 = true) := by
      rw [Finset.mem_filter]
      refine ⟨hmem, ?_⟩
      have : (knNegLabel l).1 = true := by
        rw [knNegLabel]
        simp [hl1]
      exact this
    have himg : (knNegLabel l).2 ∈ knPos (knNegCell x) :=
      Finset.mem_image.mpr ⟨knNegLabel l, hmemf, rfl⟩
    rwa [knNegLabel_snd, hll] at himg

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNegIdx_negCell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNegIdx_negCell {n : ℕ} (x : Finset (Bool × Fin n)) :
  knNegIdx (knNegCell x) = knPos x := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp hi
    have hl1 : l.1 = false := (Finset.mem_filter.mp hl).2
    obtain ⟨m, hm, hml⟩ := knMem_negCell.mp
      (Finset.mem_of_mem_filter _ hl)
    have hmb : m.1 = true := by
      have h1 := congrArg Prod.fst hml
      rw [hl1] at h1
      have hfst : (knNegLabel m).1 = (!m.1) := rfl
      rw [hfst] at h1
      cases hm1 : m.1 <;> simp_all
    have hmi : m.2 = i := by
      have h2 := congrArg Prod.snd hml
      simp only [knNegLabel] at h2
      omega
    have hmem : (true, i) ∈ x.filter (fun l => l.1 = true) := by
      rw [Finset.mem_filter]
      refine ⟨?_, rfl⟩
      have hme : m = (true, m.2) := Prod.ext hmb rfl
      rw [hme] at hm
      rwa [hmi] at hm
    exact Finset.mem_image.mpr ⟨(true, i), hmem, rfl⟩
  · intro hi
    obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp hi
    have hl1 : l.1 = true := (Finset.mem_filter.mp hl).2
    have hlm : l ∈ x := Finset.mem_of_mem_filter _ hl
    have hmem : knNegLabel l ∈ knNegCell x := knNegLabel_mem_negCell hlm
    have hmemf : knNegLabel l ∈
      (knNegCell x).filter (fun l => l.1 = false) := by
      rw [Finset.mem_filter]
      refine ⟨hmem, ?_⟩
      have hfl : (knNegLabel l).1 = false := by
        rw [knNegLabel]
        simp [hl1]
      exact hfl
    have himg : (knNegLabel l).2 ∈ knNegIdx (knNegCell x) :=
      Finset.mem_image.mpr ⟨knNegLabel l, hmemf, rfl⟩
    rwa [knNegLabel_snd, hll] at himg

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knPos_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knPos_mono {n : ℕ} {x y : Finset (Bool × Fin n)}
  (h : x ⊆ y) : knPos x ⊆ knPos y := by
  classical
  intro i hi
  obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp hi
  have hlx : l ∈ x := Finset.mem_of_mem_filter _ hl
  have hl1 : l.1 = true := (Finset.mem_filter.mp hl).2
  exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨h hlx, hl1⟩, hll⟩

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNegIdx_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNegIdx_mono {n : ℕ} {x y : Finset (Bool × Fin n)}
  (h : x ⊆ y) : knNegIdx x ⊆ knNegIdx y := by
  classical
  intro i hi
  obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp hi
  have hlx : l ∈ x := Finset.mem_of_mem_filter _ hl
  have hl1 : l.1 = false := (Finset.mem_filter.mp hl).2
  exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨h hlx, hl1⟩, hll⟩

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knFp_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knFp_mono {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
  {x y : Finset (Bool × Fin n)} (h : x ⊆ y) : knFp C x ≤ knFp C y := by
  classical
  unfold knFp
  rw [Finset.sup_le_iff]
  intro B hB
  have hBmem := Finset.mem_powersetCard.mp hB
  have hBmem2 : B ∈ Finset.powersetCard k (knPos y) :=
    Finset.mem_powersetCard.mpr ⟨hBmem.1.trans (knPos_mono h), hBmem.2⟩
  exact Finset.le_sup hBmem2

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knFm_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knFm_mono {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
  {x y : Finset (Bool × Fin n)} (h : x ⊆ y) : knFm C x ≤ knFm C y := by
  classical
  unfold knFm
  rw [Finset.sup_le_iff]
  intro B hB
  have hBmem := Finset.mem_powersetCard.mp hB
  have hBmem2 : B ∈ Finset.powersetCard k (knNegIdx y) :=
    Finset.mem_powersetCard.mpr ⟨hBmem.1.trans (knNegIdx_mono h), hBmem.2⟩
  exact Finset.le_sup hBmem2

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knConsistent_snd_inj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knConsistent_snd_inj {n : ℕ} {x : Finset (Bool × Fin n)}
  (hcons : knConsistent x) {l₁ l₂ : Bool × Fin n}
  (h₁ : l₁ ∈ x) (h₂ : l₂ ∈ x) (hsnd : l₁.2 = l₂.2) : l₁ = l₂ := by
  by_cases hb : l₁.1 = l₂.1
  · exact Prod.ext hb hsnd
  · exfalso
    have hnb : l₂.1 = !l₁.1 := by
      cases h₁b : l₁.1 <;> cases h₂b : l₂.1 <;> simp_all
    have hneg : l₂ = knNegLabel l₁ := by
      have e1 : l₂ = (l₂.1, l₂.2) := Prod.mk.eta.symm
      have e2 : knNegLabel l₁ = ((!l₁.1), l₁.2) := rfl
      rw [e1, e2, hnb, hsnd]
    exact hcons l₁ h₁ (hneg ▸ h₂)

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knFilterPos_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knFilterPos_injOn {n : ℕ} {x : Finset (Bool × Fin n)}
  (hcons : knConsistent x) :
  Set.InjOn Prod.snd (↑(x.filter (fun l => l.1 = true)) :
    Set (Bool × Fin n)) := by
  intro a ha b hb hab
  exact knConsistent_snd_inj hcons (Finset.mem_of_mem_filter _
    (Finset.mem_coe.mp ha)) (Finset.mem_of_mem_filter _
    (Finset.mem_coe.mp hb)) hab

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knFilterNeg_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knFilterNeg_injOn {n : ℕ} {x : Finset (Bool × Fin n)}
  (hcons : knConsistent x) :
  Set.InjOn Prod.snd (↑(x.filter (fun l => l.1 = false)) :
    Set (Bool × Fin n)) := by
  intro a ha b hb hab
  exact knConsistent_snd_inj hcons (Finset.mem_of_mem_filter _
    (Finset.mem_coe.mp ha)) (Finset.mem_of_mem_filter _
    (Finset.mem_coe.mp hb)) hab

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knConsistent_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knConsistent_card_eq {n : ℕ} {x : Finset (Bool × Fin n)}
  (hcons : knConsistent x) :
  x.card = (knPos x).card + (knNegIdx x).card := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (s := x) (fun l => l.1 = true)
  have hneg : x.filter (fun l => ¬ l.1 = true) =
    x.filter (fun l => l.1 = false) := by
    apply Finset.filter_congr
    intro l _
    simp only [Bool.not_eq_true]
  rw [hneg] at hpart
  have hp : (knPos x).card = (x.filter (fun l => l.1 = true)).card := by
    unfold knPos
    exact Finset.card_image_of_injOn (knFilterPos_injOn hcons)
  have hq : (knNegIdx x).card = (x.filter (fun l => l.1 = false)).card := by
    unfold knNegIdx
    exact Finset.card_image_of_injOn (knFilterNeg_injOn hcons)
  omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knPos_neg_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knPos_neg_disjoint {n : ℕ} {x : Finset (Bool × Fin n)}
  (hcons : knConsistent x) :
  Disjoint (knPos x) (knNegIdx x) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiP hiN
  obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp hiP
  obtain ⟨m, hm, hmm⟩ := Finset.mem_image.mp hiN
  have hl1 : l.1 = true := (Finset.mem_filter.mp hl).2
  have hm1 : m.1 = false := (Finset.mem_filter.mp hm).2
  have hle : l = (true, i) := Prod.ext hl1 hll
  have hme : m = (false, i) := Prod.ext hm1 hmm
  have hlt : (true, i) ∈ x := hle ▸ Finset.mem_of_mem_filter _ hl
  have hmt : (false, i) ∈ x := hme ▸ Finset.mem_of_mem_filter _ hm
  have hneg : knNegLabel (true, i) = (false, i) := rfl
  exact hcons _ hlt (hneg ▸ hmt)

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knMinIdx_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knMinIdx_mem {n : ℕ} {x : Finset (Bool × Fin n)}
  (hne : x.Nonempty) : knMinIdx x hne ∈ x.image Prod.snd :=
  Finset.min'_mem _ _

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knMinIdx_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knMinIdx_le {n : ℕ} {x : Finset (Bool × Fin n)}
  (hne : x.Nonempty) {j : Fin n} (hj : j ∈ x.image Prod.snd) :
  knMinIdx x hne ≤ j :=
  Finset.min'_le _ _ hj

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNegCell_image_snd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNegCell_image_snd {n : ℕ} (x : Finset (Bool × Fin n)) :
  (knNegCell x).image Prod.snd = x.image Prod.snd := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨l, hl, hlj⟩ := Finset.mem_image.mp hj
    obtain ⟨m, hm, hml⟩ := knMem_negCell.mp hl
    refine Finset.mem_image.mpr ⟨m, hm, ?_⟩
    rw [← hlj, ← hml]
    rfl
  · intro hj
    obtain ⟨m, hm, hmj⟩ := Finset.mem_image.mp hj
    refine Finset.mem_image.mpr ⟨knNegLabel m, knNegLabel_mem_negCell hm, ?_⟩
    rw [knNegLabel_snd, hmj]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knMinIdx_negCell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knMinIdx_negCell {n : ℕ} {x : Finset (Bool × Fin n)}
  (hne : x.Nonempty) (hneN : (knNegCell x).Nonempty) :
  knMinIdx (knNegCell x) hneN = knMinIdx x hne := by
  classical
  have himg := knNegCell_image_snd x
  have hiN : knMinIdx (knNegCell x) hneN ∈ x.image Prod.snd := by
    have h := knMinIdx_mem hneN
    rwa [himg] at h
  have hi : knMinIdx x hne ∈ (knNegCell x).image Prod.snd := by
    have h := knMinIdx_mem hne
    rwa [← himg] at h
  exact le_antisymm (knMinIdx_le hneN hi) (knMinIdx_le hne hiN)

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knTrue_mem_negCell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knTrue_mem_negCell {n : ℕ} {x : Finset (Bool × Fin n)}
  {i : Fin n} :
  (true, i) ∈ knNegCell x ↔ (false, i) ∈ x := by
  classical
  rw [knMem_negCell]
  constructor
  · rintro ⟨m, hm, hml⟩
    have h1 : m.1 = false := by
      have h := congrArg Prod.fst hml
      simpa [knNegLabel] using h
    have h2 : m.2 = i := by
      have h := congrArg Prod.snd hml
      simpa [knNegLabel] using h
    have hme : m = (false, i) := Prod.ext h1 h2
    rwa [hme] at hm
  · intro hm
    exact ⟨(false, i), hm, rfl⟩

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knFalse_mem_negCell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knFalse_mem_negCell {n : ℕ} {x : Finset (Bool × Fin n)}
  {i : Fin n} :
  (false, i) ∈ knNegCell x ↔ (true, i) ∈ x := by
  classical
  rw [knMem_negCell]
  constructor
  · rintro ⟨m, hm, hml⟩
    have h1 : m.1 = true := by
      have h := congrArg Prod.fst hml
      simpa [knNegLabel] using h
    have h2 : m.2 = i := by
      have h := congrArg Prod.snd hml
      simpa [knNegLabel] using h
    have hme : m = (true, i) := Prod.ext h1 h2
    rwa [hme] at hm
  · intro hm
    exact ⟨(true, i), hm, rfl⟩

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLab_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLab_empty {n k : ℕ}
  (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
  (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n) :
  knLab C hn hk h2 ∅ = (true, ⟨n - 1, by omega⟩) := by
  unfold knLab
  simp

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLab_small](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLab_small {n k : ℕ}
  (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
  (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n)
  {x : Finset (Bool × Fin n)} (hne : x ≠ ∅)
  (hfp : knFp C x = 0) (hfm : knFm C x = 0) :
  knLab C hn hk h2 x =
    knLabSmall x (Finset.nonempty_iff_ne_empty.mpr hne) hn := by
  unfold knLab
  simp only [dite_eq_right hne,
    dite_eq_left (show knFp C x = 0 ∧ knFm C x = 0 from ⟨hfp, hfm⟩)]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLab_large_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLab_large_pos {n k : ℕ}
  (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
  (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n)
  {x : Finset (Bool × Fin n)} (hne : x ≠ ∅)
  (hlarge : ¬ (knFp C x = 0 ∧ knFm C x = 0))
  (hpos : knFm C x < knFp C x) (hfp : 1 ≤ knFp C x) :
  knLab C hn hk h2 x = knLabLargePos C hk h2 x hfp := by
  unfold knLab
  simp only [dite_eq_right hne, dite_eq_right hlarge, dite_eq_left hpos]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLab_large_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLab_large_neg {n k : ℕ}
  (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
  (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n)
  {x : Finset (Bool × Fin n)} (hne : x ≠ ∅)
  (hlarge : ¬ (knFp C x = 0 ∧ knFm C x = 0))
  (hneg : ¬ knFm C x < knFp C x) (hfm : 1 ≤ knFm C x) :
  knLab C hn hk h2 x = knLabLargeNeg C hk h2 x hfm := by
  unfold knLab
  simp only [dite_eq_right hne, dite_eq_right hlarge, dite_eq_right hneg]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knConsistent_bool_exact](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knConsistent_bool_exact {n : ℕ} {x : Finset (Bool × Fin n)}
  (hcons : knConsistent x) {i : Fin n} (hi : i ∈ x.image Prod.snd) :
  ((true, i) ∈ x ∧ (false, i) ∉ x) ∨
    ((false, i) ∈ x ∧ (true, i) ∉ x) := by
  classical
  obtain ⟨l, hl, hli⟩ := Finset.mem_image.mp hi
  obtain ⟨b, j⟩ := l
  have hji : j = i := hli
  cases b with
  | false =>
    refine Or.inr ⟨hji ▸ hl, ?_⟩
    intro hcon
    have hcon' : (true, j) ∈ x := by rw [hji]; exact hcon
    have hneg : knNegLabel (false, j) = (true, j) := rfl
    exact hcons _ hl (hneg ▸ hcon')
  | true =>
    refine Or.inl ⟨hji ▸ hl, ?_⟩
    intro hcon
    have hcon' : (false, j) ∈ x := by rw [hji]; exact hcon
    have hpos : (true, j) ∈ x := hji ▸ hl
    have hneg : knNegLabel (true, j) = (false, j) := rfl
    exact hcons _ hpos (hneg ▸ hcon')

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLabSmall_fst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLabSmall_fst {n : ℕ} {x : Finset (Bool × Fin n)}
  {hne : x.Nonempty} {hn : 0 < n} :
  (knLabSmall x hne hn).1 = decide ((true, knMinIdx x hne) ∈ x) :=
  rfl

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLabSmall_snd_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLabSmall_snd_val {n : ℕ} {x : Finset (Bool × Fin n)}
  {hne : x.Nonempty} {hn : 0 < n} :
  ((knLabSmall x hne hn).2).val = min (x.card - 1) (n - 1) :=
  rfl

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLabLargePos_fst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLabLargePos_fst {n k : ℕ}
  {C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1))}
  {hk : 0 < k} {h2 : 2 * k ≤ n} {x : Finset (Bool × Fin n)}
  {hfp : 1 ≤ knFp C x} :
  (knLabLargePos C hk h2 x hfp).1 = true :=
  rfl

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLabLargePos_snd_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLabLargePos_snd_val {n k : ℕ}
  {C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1))}
  {hk : 0 < k} {h2 : 2 * k ≤ n} {x : Finset (Bool × Fin n)}
  {hfp : 1 ≤ knFp C x} :
  ((knLabLargePos C hk h2 x hfp).2).val = (knFp C x - 1) + 2 * (k - 1) :=
  rfl

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLabLargeNeg_fst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLabLargeNeg_fst {n k : ℕ}
  {C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1))}
  {hk : 0 < k} {h2 : 2 * k ≤ n} {x : Finset (Bool × Fin n)}
  {hfm : 1 ≤ knFm C x} :
  (knLabLargeNeg C hk h2 x hfm).1 = false :=
  rfl

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLabLargeNeg_snd_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLabLargeNeg_snd_val {n k : ℕ}
  {C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1))}
  {hk : 0 < k} {h2 : 2 * k ≤ n} {x : Finset (Bool × Fin n)}
  {hfm : 1 ≤ knFm C x} :
  ((knLabLargeNeg C hk h2 x hfm).2).val = (knFm C x - 1) + 2 * (k - 1) :=
  rfl

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knNegLabel_fst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knNegLabel_fst {n : ℕ} (l : Bool × Fin n) :
  (knNegLabel l).1 = !l.1 :=
  rfl

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knSmall_val_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knSmall_val_lt {n k : ℕ} (hk : 0 < k)
  {x : Finset (Bool × Fin n)} (xne : x.Nonempty)
  (hle : x.card ≤ 2 * k - 2) :
  min (x.card - 1) (n - 1) < 2 * (k - 1) := by
  have h1 : 1 ≤ x.card := Finset.one_le_card.mpr xne
  have h2m := Nat.min_le_left (x.card - 1) (n - 1)
  omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knSmall_val_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knSmall_val_ne {n k : ℕ} (hk : 0 < k) (h2 : 2 * k ≤ n)
  {x : Finset (Bool × Fin n)} (xne : x.Nonempty)
  (hle : x.card ≤ 2 * k - 2) :
  min (x.card - 1) (n - 1) ≠ n - 1 := by
  have h1 : 1 ≤ x.card := Finset.one_le_card.mpr xne
  have h2m := Nat.min_le_left (x.card - 1) (n - 1)
  omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLarge_val_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLarge_val_le {n k : ℕ} (hk : 0 < k) (h2 : 2 * k ≤ n)
  (f : ℕ) (hf1 : 1 ≤ f) (hfN : f ≤ n - 2 * k + 1) :
  (f - 1) + 2 * (k - 1) ≤ n - 2 := by
  omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knLarge_val_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knLarge_val_ne {n k : ℕ} (hk : 0 < k) (h2 : 2 * k ≤ n)
  (f : ℕ) (hf1 : 1 ≤ f) (hfN : f ≤ n - 2 * k + 1) :
  (f - 1) + 2 * (k - 1) ≠ n - 1 := by
  have hle := knLarge_val_le hk h2 f hf1 hfN
  omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knFp_negCell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knFp_negCell {n k N : ℕ}
  (C : (kneserGraph n k).Coloring (Fin N))
  (x : Finset (Bool × Fin n)) :
  knFp C (knNegCell x) = knFm C x := by
  unfold knFp knFm
  rw [knPos_negCell]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[knFm_negCell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma knFm_negCell {n k N : ℕ}
  (C : (kneserGraph n k).Coloring (Fin N))
  (x : Finset (Bool × Fin n)) :
  knFm C (knNegCell x) = knFp C x := by
  unfold knFp knFm
  rw [knNegIdx_negCell]

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

/--
[kneser_lovasz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean)
-/
@[path]
private lemma kneser_lovasz_eq
  {n k : ℕ}
-- given
  (hk : 0 < k)
  (h : 2 * k ≤ n) :
-- imply
  (kneserGraph n k).chromaticNumber = (n - 2 * k + 2 : ℕ∞) := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted.kneser_lovasz hk h


-- created on 2026-10-20
-- updated on 2026-10-26
