import sympy.sets.stirling_partition
import sympy.Basic
import Lemma.Finset.Subset_Range.of.In_Conditionset
import Lemma.Finset.NcardImageConditionset.eq.NcardImageImageConditionset
import Lemma.Finset.SetOfIn_ImageConditionset_Add_1Add_1AndFinset.eq.J
import Lemma.Finset.SetOfIn_ImageConditionsetAndInFinset.eq.ImageImageConditionset
import Lemma.Finset.Injective.of.In_Conditionset
import Lemma.Finset.FiniteParts
import Lemma.Finset.EqCard.of.In_Parts
open Finset Stirling.conditionset


@[main]
private lemma main
-- given
  (n k : ℕ) :
-- imply
  (parts (n + 1) (k + 1)).ncard = (parts n k).ncard + (k + 1) * (parts n (k + 1)).ncard := by
-- proof
  set S1 := {e | e ∈ parts (n + 1) (k + 1) ∧ ({n} : Finset ℕ) ∈ e} with hS1
  set S2 := {e | e ∈ parts (n + 1) (k + 1) ∧ ({n} : Finset ℕ) ∉ e} with hS2d
  have hU : parts (n + 1) (k + 1) = S1 ∪ S2 := by
    ext e
    simp only [hS1, hS2d, Set.mem_union, Set.mem_ofPred_eq]
    tauto
  have hfin := FiniteParts (n + 1) (k + 1)
  have hD : Disjoint S1 S2 := Set.disjoint_left.mpr fun e h1 h2 => h2.2 h1.2
  rw [hU, Set.ncard_union_eq hD (hfin.subset fun e h => h.1) (hfin.subset fun e h => h.1)]
  congr 1
  ·
    rw [show S1 = _ from SetOfIn_ImageConditionsetAndInFinset.eq.ImageImageConditionset]
    exact NcardImageConditionset.eq.NcardImageImageConditionset.symm
  set T : Set (Finset (Finset ℕ) × Finset ℕ) := {p | p.1 ∈ parts n (k + 1) ∧ p.2 ∈ p.1} with hTd
  set g : Finset (Finset ℕ) × Finset ℕ → Finset (Finset ℕ) := fun p => insert (insert n p.2) (p.1.erase p.2) with hg
  have key : ∀ y ∈ Stirling.conditionset n (k + 1), ∀ j,
      Finset.univ.image (Function.update y j (insert n (y j))) = g (Finset.univ.image y, y j) := by
    intro y hy j
    ext b
    simp only [hg, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase]
    constructor
    ·
      rintro ⟨i, rfl⟩
      if hij : i = j then
        subst hij
        left
        simp
      else
        right
        rw [Function.update_of_ne hij]
        exact ⟨fun h => hij (Injective.of.In_Conditionset hy h), i, rfl⟩
    ·
      rintro (rfl | ⟨hne, i, rfl⟩)
      · exact ⟨j, by simp⟩
      ·
        have hij : i ≠ j := fun h => hne (h ▸ rfl)
        exact ⟨i, by rw [Function.update_of_ne hij]⟩
  have hS2 : S2 = g '' T := by
    rw [show S2 = _ from SetOfIn_ImageConditionset_Add_1Add_1AndFinset.eq.J]
    ext e
    simp only [Set.mem_iUnion, Set.mem_image]
    constructor
    ·
      rintro ⟨j, y, hy, rfl⟩
      exact ⟨(Finset.univ.image y, y j), ⟨⟨y, hy, rfl⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, (key y hy j).symm⟩
    ·
      rintro ⟨⟨P, b⟩, ⟨⟨y, hy, rfl⟩, hb⟩, rfl⟩
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
      exact ⟨j, y, hy, key y hy j⟩
  have hinj : Set.InjOn g T := by
    rintro ⟨P, b⟩ ⟨⟨y, hy, rfl⟩, hb⟩ ⟨P', b'⟩ ⟨⟨y', hy', rfl⟩, hb'⟩ heq
    simp only [hg] at heq hb hb'
    have hnP : ∀ c ∈ Finset.univ.image y, n ∉ c := by
      intro c hc hn
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
      simpa using Subset_Range.of.In_Conditionset hy i hn
    have hnP' : ∀ c ∈ Finset.univ.image y', n ∉ c := by
      intro c hc hn
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
      simpa using Subset_Range.of.In_Conditionset hy' i hn
    have hbb : insert n b = insert n b' := by
      have : insert n b ∈ insert (insert n b') ((Finset.univ.image y').erase b') := heq ▸ Finset.mem_insert_self _ _
      obtain h | h := Finset.mem_insert.mp this
      · exact h
      · exact absurd (Finset.mem_insert_self n b) (hnP' _ (Finset.mem_of_mem_erase h))
    have hb_eq : b = b' := by
      have := congrArg (fun s => s.erase n) hbb
      rwa [Finset.erase_insert (hnP b hb), Finset.erase_insert (hnP' b' hb')] at this
    subst hb_eq
    have hPe : (Finset.univ.image y).erase b = (Finset.univ.image y').erase b := by
      have := congrArg (fun s => s.erase (insert n b)) heq
      have h1 : insert n b ∉ (Finset.univ.image y).erase b :=
        fun h => hnP _ (Finset.mem_of_mem_erase h) (Finset.mem_insert_self _ _)
      have h2 : insert n b ∉ (Finset.univ.image y').erase b :=
        fun h => hnP' _ (Finset.mem_of_mem_erase h) (Finset.mem_insert_self _ _)
      rwa [Finset.erase_insert h1, Finset.erase_insert h2] at this
    refine Prod.ext ?_ rfl
    show Finset.univ.image y = Finset.univ.image y'
    rw [← Finset.insert_erase hb, ← Finset.insert_erase hb', hPe]
  have hT : T.ncard = (k + 1) * (parts n (k + 1)).ncard := by
    have hf := FiniteParts n (k + 1)
    have hTF : T = ↑(hf.toFinset.biUnion (fun P => P.image (fun b => (P, b)))) := by
      ext ⟨P, b⟩
      simp only [hTd, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image, Set.Finite.mem_toFinset]
      constructor
      ·
        rintro ⟨hP, hb⟩
        exact ⟨P, hP, b, hb, rfl⟩
      ·
        rintro ⟨Q, hQ, c, hc, h⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨hQ, hc⟩
    have hc : ∀ P ∈ hf.toFinset, (P.image (fun b => (P, b))).card = k + 1 := fun P hP => by
      rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2), EqCard.of.In_Parts (hf.mem_toFinset.mp hP)]
    rw [hTF, Set.ncard_coe_finset, Finset.card_biUnion, Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul,
      Set.ncard_eq_toFinset_card _ hf, mul_comm]
    intro P _ Q _ hPQ
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro p h1 h2
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨c, -, hc'⟩ := Finset.mem_image.mp h2
    exact hPQ (congrArg Prod.fst hc').symm
  rw [hS2, hinj.ncard_image, hT]


-- created on 2026-10-07
