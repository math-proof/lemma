import sympy.functions.combinatorial.numbers
import sympy.sets.partition
import Mathlib.Tactic

open Finset

/-! Facts about `Stirling.conditionset` (ordered set partitions): blocks lie in `range n`, distinct blocks
are disjoint, the `s0_B` / `s2_A` / `s2_B` decompositions, and the identification of the number of
unordered partitions with Mathlib's `Nat.stirlingSecond` via the recurrence. -/

namespace Stirling.conditionset

theorem sub_range {n k : ℕ} {x : Fin k → Finset ℕ} (hx : x ∈ Stirling.conditionset n k) (i : Fin k) :
    x i ⊆ Finset.range n := by
  rw [← hx.1]
  exact Finset.subset_biUnion_of_mem x (Finset.mem_univ i)

theorem disj {n k : ℕ} {x : Fin k → Finset ℕ} (hx : x ∈ Stirling.conditionset n k) {a : ℕ} {i1 i2 : Fin k}
    (h1 : a ∈ x i1) (h2 : a ∈ x i2) : i1 = i2 := by
  set w : ℕ → Finset ℕ := fun i => if h : i < k then x ⟨i, h⟩ else ∅ with hw
  have h₀ : ∑ i ∈ Finset.range k, (w i).card = n := by
    rw [← hx.2.1, ← Fin.sum_univ_eq_sum_range (fun i => (w i).card)]
    simp [hw]
  have h₁ : (Finset.range k).biUnion w = Finset.range n := by
    rw [← hx.1]
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, ha⟩
      exact ⟨⟨i, hi⟩, by simpa [hw, hi] using ha⟩
    · rintro ⟨i, ha⟩
      exact ⟨i, i.isLt, by simpa [hw, i.isLt] using ha⟩
  exact Fin.ext (Finset.eq_of_mem_of_sum_card_eq h₀ h₁ i1.isLt i2.isLt (by simpa [hw] using h1) (by simpa [hw] using h2))

theorem s0_B {n k : ℕ} :
    ((fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k).ncard =
    ((fun e : Finset (Finset ℕ) => insert ({n} : Finset ℕ) e) '' ((fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k)).ncard := by
  symm
  apply Set.InjOn.ncard_image
  have hn : ∀ e ∈ (fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k, ({n} : Finset ℕ) ∉ e := by
    rintro e ⟨x, hx, rfl⟩ hmem
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    have := sub_range hx i (hi ▸ Finset.mem_singleton_self n)
    simp at this
  intro e1 h1 e2 h2 heq
  have := congrArg (fun s => Finset.erase s ({n} : Finset ℕ)) heq
  simpa [Finset.erase_insert (hn e1 h1), Finset.erase_insert (hn e2 h2)] using this

theorem s2_A {n k : ℕ} :
    {e | e ∈ (fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset (n + 1) (k + 1) ∧ ({n} : Finset ℕ) ∉ e} =
    ⋃ j : Fin (k + 1), (fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image (Function.update x j (insert n (x j)))) '' Stirling.conditionset n (k + 1) := by
  ext e
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hne⟩
    have hnU : n ∈ Finset.univ.biUnion x := by rw [hx.1]; simp
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hnU
    have hout : ∀ i, i ≠ j → n ∉ x i := fun i hi hni => hi (disj hx hni hj)
    set y : Fin (k + 1) → Finset ℕ := fun i => (x i).erase n with hy
    have hupd : Function.update y j (insert n (y j)) = x := by
      funext i
      by_cases hij : i = j
      · subst hij
        simp [hy, Finset.insert_erase hj]
      · rw [Function.update_of_ne hij, hy]
        exact Finset.erase_eq_of_notMem (hout i hij)
    refine ⟨j, y, ⟨?_, ?_, ?_⟩, by rw [hupd]⟩
    · ext a
      have hU := congrArg (a ∈ ·) hx.1
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, eq_iff_iff] at hU
      simp only [hy, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, Finset.mem_erase]
      constructor
      · rintro ⟨i, hne', hi⟩
        have := hU.mp ⟨i, hi⟩
        omega
      · intro ha
        obtain ⟨i, hi⟩ := hU.mpr (by omega)
        exact ⟨i, by omega, hi⟩
    · have hc : ∀ i, (y i).card + (if i = j then 1 else 0) = (x i).card := by
        intro i
        by_cases hij : i = j
        · subst hij
          simp [hy, Finset.card_erase_add_one hj]
        · simp [hy, hij, Finset.erase_eq_of_notMem (hout i hij)]
      have := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hc i)
      rw [Finset.sum_add_distrib, hx.2.1, Finset.sum_ite_eq'] at this
      simp at this
      omega
    · intro i
      by_cases hij : i = j
      · subst hij
        have hxj : x i ≠ {n} := fun h => hne (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
        have h1 : 1 < (x i).card := by
          by_contra hle
          have hc1 : (x i).card = 1 := by have := hx.2.2 i; omega
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc1
          rw [ha] at hj hxj
          simp at hj
          exact hxj (by rw [hj])
        have := Finset.card_erase_add_one hj
        simp only [hy]
        omega
      · simp only [hy, Finset.erase_eq_of_notMem (hout i hij)]
        exact hx.2.2 i
  · rintro ⟨j, x, hx, rfl⟩
    have hsub := sub_range hx
    have hnj : n ∉ x j := fun h => by simpa using hsub j h
    refine ⟨⟨Function.update x j (insert n (x j)), ⟨?_, ?_, ?_⟩, rfl⟩, ?_⟩
    · ext a
      have hU := congrArg (a ∈ ·) hx.1
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, eq_iff_iff] at hU
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨i, hi⟩
        by_cases hij : i = j
        · subst hij
          rw [Function.update_self, Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · omega
          · have := hU.mp ⟨i, hi⟩; omega
        · rw [Function.update_of_ne hij] at hi
          have := hU.mp ⟨i, hi⟩; omega
      · intro ha
        by_cases han : a = n
        · exact ⟨j, by rw [Function.update_self, han]; exact Finset.mem_insert_self _ _⟩
        · obtain ⟨i, hi⟩ := hU.mpr (by omega)
          by_cases hij : i = j
          · subst hij
            exact ⟨i, by rw [Function.update_self]; exact Finset.mem_insert_of_mem hi⟩
          · exact ⟨i, by rw [Function.update_of_ne hij]; exact hi⟩
    · have hc : ∀ i, (Function.update x j (insert n (x j)) i).card = (x i).card + (if i = j then 1 else 0) := by
        intro i
        by_cases hij : i = j
        · subst hij
          simp [Finset.card_insert_of_notMem hnj]
        · simp [hij]
      rw [Finset.sum_congr rfl (fun i _ => hc i), Finset.sum_add_distrib, hx.2.1, Finset.sum_ite_eq']
      simp
    · intro i
      by_cases hij : i = j
      · subst hij
        rw [Function.update_self]
        exact Finset.card_pos.mpr ⟨n, Finset.mem_insert_self _ _⟩
      · rw [Function.update_of_ne hij]
        exact hx.2.2 i
    · intro hmem
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
      by_cases hij : i = j
      · subst hij
        rw [Function.update_self] at hi
        have hxe : x i ⊆ {n} := fun a ha => hi ▸ Finset.mem_insert_of_mem ha
        obtain ⟨a, ha⟩ := Finset.card_pos.mp (hx.2.2 i)
        have := hxe ha
        rw [Finset.mem_singleton] at this
        exact hnj (this ▸ ha)
      · rw [Function.update_of_ne hij] at hi
        have := hsub i (hi ▸ Finset.mem_singleton_self n)
        simp at this

theorem s2_B {n k : ℕ} :
    {e | e ∈ (fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset (n + 1) (k + 1) ∧ ({n} : Finset ℕ) ∈ e} =
    (fun e : Finset (Finset ℕ) => insert ({n} : Finset ℕ) e) '' ((fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k) := by
  ext e
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hmem⟩
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
    have hout : ∀ i, i ≠ j → n ∉ x i := fun i hi hni => hi (disj hx hni (by rw [hj]; exact Finset.mem_singleton_self n))
    refine ⟨Finset.univ.image (fun i : Fin k => x (j.succAbove i)), ⟨fun i => x (j.succAbove i), ⟨?_, ?_, ?_⟩, rfl⟩, ?_⟩
    · ext a
      have hU := congrArg (a ∈ ·) hx.1
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, eq_iff_iff] at hU ⊢
      constructor
      · rintro ⟨i, hi⟩
        have h1 := hU.mp ⟨_, hi⟩
        have : a ≠ n := fun h => hout _ (Fin.succAbove_ne j i) (h ▸ hi)
        omega
      · intro ha
        obtain ⟨i, hi⟩ := hU.mpr (by omega)
        have hij : i ≠ j := by
          rintro rfl
          rw [hj, Finset.mem_singleton] at hi
          omega
        obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hij
        exact ⟨z, hz ▸ hi⟩
    · have := hx.2.1
      rw [Fin.sum_univ_succAbove _ j, hj, Finset.card_singleton] at this
      show ∑ i, (x (j.succAbove i)).card = n
      omega
    · intro i
      exact hx.2.2 _
    · ext P
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro (rfl | ⟨i, rfl⟩)
        · exact ⟨j, hj⟩
        · exact ⟨_, rfl⟩
      · rintro ⟨i, rfl⟩
        by_cases hij : i = j
        · subst hij
          exact Or.inl hj
        · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hij
          exact Or.inr ⟨z, by rw [hz]⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨⟨(Fin.cons ({n} : Finset ℕ) y : Fin (k + 1) → Finset ℕ), ⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · ext a
      have hU := congrArg (a ∈ ·) hy.1
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, eq_iff_iff] at hU ⊢
      rw [Fin.exists_fin_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Finset.mem_singleton]
      constructor
      · rintro (rfl | ⟨i, hi⟩)
        · omega
        · have := hU.mp ⟨i, hi⟩
          omega
      · intro ha
        by_cases han : a = n
        · exact Or.inl han
        · exact Or.inr (hU.mpr (by omega))
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Finset.card_singleton, hy.2.1]
      omega
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · simpa using hy.2.2 i
    · ext P
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
      rw [Fin.exists_fin_succ]
      constructor
      · rintro (h | ⟨i, h⟩)
        · left
          rw [← h, Fin.cons_zero]
        · right
          exact ⟨i, by rw [← h, Fin.cons_succ]⟩
      · rintro (h | ⟨i, h⟩)
        · left
          rw [h, Fin.cons_zero]
        · right
          exact ⟨i, by rw [← h, Fin.cons_succ]⟩
    · exact Finset.mem_insert_self _ _


/-- The set of (unordered) partitions of `range n` into `k` blocks, as block sets of ordered partitions. -/
abbrev parts (n k : ℕ) : Set (Finset (Finset ℕ)) :=
  (fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k

theorem inj {n k : ℕ} {x : Fin k → Finset ℕ} (hx : x ∈ Stirling.conditionset n k) : Function.Injective x := by
  intro i j h
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (hx.2.2 i)
  exact disj hx ha (h ▸ ha)

theorem parts_finite (n k : ℕ) : (parts n k).Finite := by
  refine (Finset.finite_toSet ((Finset.range n).powerset.powerset)).subset ?_
  rintro e ⟨x, hx, rfl⟩
  rw [Finset.mem_coe, Finset.mem_powerset]
  intro b hb
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
  exact Finset.mem_powerset.mpr (sub_range hx i)

theorem card_of_mem {n k : ℕ} {e : Finset (Finset ℕ)} (he : e ∈ parts n k) : e.card = k := by
  obtain ⟨x, hx, rfl⟩ := he
  rw [Finset.card_image_of_injective _ (inj hx), Finset.card_univ, Fintype.card_fin]

theorem ncard_zero_zero : (parts 0 0).ncard = 1 := by
  have : parts 0 0 = {∅} := by
    ext e
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, -, rfl⟩
      simp
    · rintro rfl
      exact ⟨Fin.elim0, ⟨by simp, by simp, fun i => i.elim0⟩, by simp⟩
  rw [this, Set.ncard_singleton]

theorem ncard_zero_succ (k : ℕ) : (parts 0 (k + 1)).ncard = 0 := by
  have : parts 0 (k + 1) = ∅ := by
    ext e
    simp only [Set.mem_image, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro x hx _
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (hx.2.2 0)
    have := sub_range hx 0 ha
    simp at this
  rw [this, Set.ncard_empty]

theorem ncard_succ_zero (n : ℕ) : (parts (n + 1) 0).ncard = 0 := by
  have : parts (n + 1) 0 = ∅ := by
    ext e
    simp only [Set.mem_image, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro x hx _
    have : n ∈ Finset.univ.biUnion x := by rw [hx.1]; simp
    simp at this
  rw [this, Set.ncard_empty]

theorem ncard_succ_succ (n k : ℕ) :
    (parts (n + 1) (k + 1)).ncard = (parts n k).ncard + (k + 1) * (parts n (k + 1)).ncard := by
  set S1 := {e | e ∈ parts (n + 1) (k + 1) ∧ ({n} : Finset ℕ) ∈ e} with hS1
  set S2 := {e | e ∈ parts (n + 1) (k + 1) ∧ ({n} : Finset ℕ) ∉ e} with hS2d
  have hU : parts (n + 1) (k + 1) = S1 ∪ S2 := by
    ext e
    simp only [hS1, hS2d, Set.mem_union, Set.mem_ofPred_eq]
    tauto
  have hfin := parts_finite (n + 1) (k + 1)
  have hD : Disjoint S1 S2 := Set.disjoint_left.mpr fun e h1 h2 => h2.2 h1.2
  rw [hU, Set.ncard_union_eq hD (hfin.subset fun e h => h.1) (hfin.subset fun e h => h.1)]
  congr 1
  · rw [show S1 = _ from s2_B]
    exact s0_B.symm
  set T : Set (Finset (Finset ℕ) × Finset ℕ) := {p | p.1 ∈ parts n (k + 1) ∧ p.2 ∈ p.1} with hTd
  set g : Finset (Finset ℕ) × Finset ℕ → Finset (Finset ℕ) := fun p => insert (insert n p.2) (p.1.erase p.2) with hg
  have key : ∀ y ∈ Stirling.conditionset n (k + 1), ∀ j,
      Finset.univ.image (Function.update y j (insert n (y j))) = g (Finset.univ.image y, y j) := by
    intro y hy j
    ext b
    simp only [hg, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨i, rfl⟩
      by_cases hij : i = j
      · subst hij
        left
        simp
      · right
        rw [Function.update_of_ne hij]
        exact ⟨fun h => hij (inj hy h), i, rfl⟩
    · rintro (rfl | ⟨hne, i, rfl⟩)
      · exact ⟨j, by simp⟩
      · have hij : i ≠ j := fun h => hne (h ▸ rfl)
        exact ⟨i, by rw [Function.update_of_ne hij]⟩
  have hS2 : S2 = g '' T := by
    rw [show S2 = _ from s2_A]
    ext e
    simp only [Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨j, y, hy, rfl⟩
      exact ⟨(Finset.univ.image y, y j), ⟨⟨y, hy, rfl⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, (key y hy j).symm⟩
    · rintro ⟨⟨P, b⟩, ⟨⟨y, hy, rfl⟩, hb⟩, rfl⟩
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
      exact ⟨j, y, hy, key y hy j⟩
  have hinj : Set.InjOn g T := by
    rintro ⟨P, b⟩ ⟨⟨y, hy, rfl⟩, hb⟩ ⟨P', b'⟩ ⟨⟨y', hy', rfl⟩, hb'⟩ heq
    simp only [hg] at heq hb hb'
    have hnP : ∀ c ∈ Finset.univ.image y, n ∉ c := by
      intro c hc hn
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
      simpa using sub_range hy i hn
    have hnP' : ∀ c ∈ Finset.univ.image y', n ∉ c := by
      intro c hc hn
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
      simpa using sub_range hy' i hn
    have hbb : insert n b = insert n b' := by
      have : insert n b ∈ insert (insert n b') ((Finset.univ.image y').erase b') := heq ▸ Finset.mem_insert_self _ _
      rcases Finset.mem_insert.mp this with h | h
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
    have hf := parts_finite n (k + 1)
    have hTF : T = ↑(hf.toFinset.biUnion (fun P => P.image (fun b => (P, b)))) := by
      ext ⟨P, b⟩
      simp only [hTd, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨hP, hb⟩
        exact ⟨P, hP, b, hb, rfl⟩
      · rintro ⟨Q, hQ, c, hc, h⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨hQ, hc⟩
    have hc : ∀ P ∈ hf.toFinset, (P.image (fun b => (P, b))).card = k + 1 := fun P hP => by
      rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2), card_of_mem (hf.mem_toFinset.mp hP)]
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

theorem stirlingSecond_eq_ncard (n k : ℕ) : Nat.stirlingSecond n k = (parts n k).ncard := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rw [ncard_zero_zero, Nat.stirlingSecond_zero]
    | succ k => rw [ncard_zero_succ, Nat.stirlingSecond_zero_succ]
  | succ n ih =>
    cases k with
    | zero => rw [ncard_succ_zero, Nat.stirlingSecond_succ_zero]
    | succ k =>
      rw [Nat.stirlingSecond_succ_succ, ncard_succ_succ, ← ih, ← ih]
      ring

end Stirling.conditionset
