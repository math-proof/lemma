import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.BellWeakExcedance.Part11
open MetaMathlibExt


namespace MetaMathlibExt

/--
[card_finpartition_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean)
-/
@[path]
private lemma card_finpartition_empty (n : ℕ) :
  Fintype.card (Finpartition (∅ : Finset (Fin n))) = 1 := by
  have hU : Unique (Finpartition (∅ : Finset (Fin n))) := inferInstanceAs
    (Unique (Finpartition (⊥ : Finset (Fin n))))
  exact Fintype.card_unique

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_finpartition_eq_bell_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean)
-/
@[path]
private lemma card_finpartition_eq_bell_aux (n : ℕ) (m : ℕ) :
  ∀ T : Finset (Fin n), T.card = m →
    Fintype.card (Finpartition T) = Nat.bell m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro T hcard
    by_cases hT0 : T.card = 0
    · have hTe : T = ∅ := Finset.card_eq_zero.mp hT0
      subst hTe
      rw [card_finpartition_empty]
      rw [hT0] at hcard
      rwa [← hcard]
    · obtain ⟨m0, hm0⟩ : T.Nonempty := by
      rw [← Finset.card_pos]
      exact Nat.pos_of_ne_zero hT0
      have hcard_eq : Fintype.card (Finpartition T) =
        ∑ B : Finset (Fin n),
          Fintype.card { P : Finpartition T // P.part m0 = B } := by
        have hEquiv : Finpartition T ≃
          (Σ B : Finset (Fin n), { P : Finpartition T // P.part m0 = B }) :=
          (Equiv.sigmaFiberEquiv (fun P : Finpartition T => P.part m0)).symm
        rw [Fintype.card_congr hEquiv, Fintype.card_sigma]
      have hfiber : ∀ B : Finset (Fin n),
        Fintype.card { P : Finpartition T // P.part m0 = B } =
          (if m0 ∈ B ∧ B ⊆ T then Nat.bell (T.card - B.card) else 0) := by
        intro B
        by_cases hB : m0 ∈ B ∧ B ⊆ T
        · have hmB : m0 ∈ B := hB.1
          have hsub : B ⊆ T := hB.2
          have hEquiv := fiberEquiv m0 hmB hsub
          have hcard2 : Fintype.card { P : Finpartition T // P.part m0 = B } =
            Fintype.card (Finpartition (T \ B)) :=
            Fintype.card_congr hEquiv
          have hlt : (T \ B).card < m := by
            have hpos : 0 < B.card := Finset.card_pos.mpr ⟨m0, hmB⟩
            have hle : B.card ≤ T.card := Finset.card_le_card hsub
            have hsd : (T \ B).card = T.card - B.card :=
              Finset.card_sdiff_of_subset hsub
            omega
          have hIH := ih ((T \ B).card) hlt (T \ B) rfl
          have hsd : (T \ B).card = T.card - B.card :=
            Finset.card_sdiff_of_subset hsub
          rw [hcard2, hIH, hsd]
          simp [hB]
        · have hEmpty : IsEmpty { P : Finpartition T // P.part m0 = B } :=
          ⟨fun ⟨P, hP⟩ => by
            have hmB : m0 ∈ B := by
              have hmem : m0 ∈ P.part m0 := P.mem_part hm0
              rwa [hP] at hmem
            have hsub : B ⊆ T := by
              have hss : P.part m0 ⊆ T := P.part_subset m0
              rwa [hP] at hss
            exact hB ⟨hmB, hsub⟩⟩
          rw [Fintype.card_eq_zero]
          simp [hB]
      rw [hcard_eq]
      simp only [hfiber]
      have hsum : (∑ B : Finset (Fin n),
        (if m0 ∈ B ∧ B ⊆ T then Nat.bell (T.card - B.card) else 0)) =
        ∑ B ∈ Finset.univ.filter (fun B => m0 ∈ B ∧ B ⊆ T),
          Nat.bell (T.card - B.card) := by
        rw [Finset.sum_filter]
      have hfilter_eq : Finset.univ.filter (fun B : Finset (Fin n) => m0 ∈ B ∧ B ⊆ T) =
        (T.powerset.filter (fun B => m0 ∈ B)) := by
        ext B
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_powerset]
        constructor
        · intro h
          exact ⟨h.2, h.1⟩
        · intro h
          exact ⟨h.2, h.1⟩
      rw [hsum, hfilter_eq]
      set E : Finset (Fin n) := T.erase m0 with hE
      have hm0E : m0 ∉ E := Finset.notMem_erase m0 T
      have hTE : T = insert m0 E := (Finset.insert_erase hm0).symm
      have hcardE : E.card + 1 = m := by
        have hce : E.card = T.card - 1 := Finset.card_erase_of_mem hm0
        omega
      have himage : T.powerset.filter (fun B => m0 ∈ B) =
        E.powerset.image (fun U => insert m0 U) := by
        ext B
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
        constructor
        · intro h
          obtain ⟨hsub, hmB⟩ := h
          refine ⟨B.erase m0, ?_, Finset.insert_erase hmB⟩
          intro x hx
          rw [Finset.mem_erase] at hx
          rw [hE, Finset.mem_erase]
          exact ⟨hx.1, hsub hx.2⟩
        · intro h
          obtain ⟨U, hU, rfl⟩ := h
          constructor
          · intro x hx
            rw [Finset.mem_insert] at hx
            obtain rfl | hUx := hx
            · exact hm0
            · exact Finset.mem_of_mem_erase (hE ▸ hU hUx)
          · exact Finset.mem_insert_self m0 U
      rw [himage]
      have hinj : ∀ U1 ∈ E.powerset, ∀ U2 ∈ E.powerset,
        insert m0 U1 = insert m0 U2 → U1 = U2 := by
        intro U1 hU1 U2 hU2 hEq
        have h1 : m0 ∉ U1 := by
          have hsub1 : U1 ⊆ E := Finset.mem_powerset.mp hU1
          exact fun h => hm0E (hE ▸ hsub1 h)
        have h2 : m0 ∉ U2 := by
          have hsub2 : U2 ⊆ E := Finset.mem_powerset.mp hU2
          exact fun h => hm0E (hE ▸ hsub2 h)
        have hc := congrArg (fun S => S.erase m0) hEq
        simp only [Finset.erase_insert h1, Finset.erase_insert h2] at hc
        exact hc
      rw [Finset.sum_image hinj]
      have hterm : ∀ U ∈ E.powerset,
        T.card - (insert m0 U).card = E.card - U.card := by
        intro U hU
        have hsub : U ⊆ E := Finset.mem_powerset.mp hU
        have hnot : m0 ∉ U := fun h => hm0E (hE ▸ hsub h)
        have hcIns : (insert m0 U).card = U.card + 1 :=
          Finset.card_insert_of_notMem hnot
        have hle : U.card ≤ E.card := Finset.card_le_card hsub
        omega
      have hsum2 : (∑ U ∈ E.powerset, Nat.bell (T.card - (insert m0 U).card)) =
        ∑ U ∈ E.powerset, Nat.bell (E.card - U.card) := by
        apply Finset.sum_congr rfl
        intro U hU
        rw [hterm U hU]
      rw [hsum2]
      have hmaps : ∀ U ∈ E.powerset, U.card ∈ Finset.range (E.card + 1) := by
        intro U hU
        rw [Finset.mem_range]
        have hsub : U ⊆ E := Finset.mem_powerset.mp hU
        have hle : U.card ≤ E.card := Finset.card_le_card hsub
        omega
      have hfib := Finset.sum_fiberwise_of_maps_to hmaps
        (fun U => Nat.bell (E.card - U.card))
      rw [← hfib]
      have hinner : ∀ i ∈ Finset.range (E.card + 1),
        (∑ U ∈ E.powerset.filter (fun U => U.card = i),
          Nat.bell (E.card - U.card)) =
          Nat.choose E.card i * Nat.bell (E.card - i) := by
        intro i hi
        have hfilter : E.powerset.filter (fun U => U.card = i) =
          E.powersetCard i := by
          ext U
          simp only [Finset.mem_filter, Finset.mem_powerset,
            Finset.mem_powersetCard]
        rw [hfilter]
        have hconst : ∀ U ∈ E.powersetCard i,
          Nat.bell (E.card - U.card) = Nat.bell (E.card - i) := by
          intro U hU
          rw [Finset.mem_powersetCard] at hU
          rw [hU.2]
        rw [Finset.sum_congr rfl hconst]
        rw [Finset.sum_const, Finset.card_powersetCard]
        simp only [smul_eq_mul]
      rw [Finset.sum_congr rfl hinner]
      have hbell := Nat.bell_succ E.card
      rw [← hcardE] at hcard ⊢
      -- hcard : T.card = E.card + 1, goal: ∑ i ∈ range, ... = bell (E.card+1)
      rw [hbell]
      rw [← Nat.range_succ_eq_Iic]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_finpartition_univ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean)
-/
@[path]
private lemma card_finpartition_univ (n : ℕ) :
  Fintype.card (Finpartition (Finset.univ : Finset (Fin n))) = Nat.bell n := by
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by
    simp only [Finset.card_univ, Fintype.card_fin]
  exact card_finpartition_eq_bell_aux n n _ hcard

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bell_count_perm_increasing_weakExcedance_letters](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean)
-/
@[path]
lemma bell_count_perm_increasing_weakExcedance_letters
  {n : ℕ} :
-- imply
  Fintype.card { σ : Equiv.Perm (Fin n) //
    ∀ i j : Fin n, i < j → i ≤ σ i → j ≤ σ j → σ i < σ j } = Nat.bell n := by
-- proof
  exact (Fintype.card_congr (bwe_validPermEquivFinpartition n)).trans
    (card_finpartition_univ n)
end MetaMathlibExt



-- created on 2026-10-20
-- updated on 2026-10-26
