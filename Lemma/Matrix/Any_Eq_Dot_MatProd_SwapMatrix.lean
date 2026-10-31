import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic
import Lemma.Matrix.AppendHstackS.eq.MatProd_SwapMatrix.of.Le
import Lemma.Matrix.EqDotDot_SwapMatrix
import Lemma.Matrix.GetDot_SwapMatrix.eq.Get
import Lemma.Matrix.MatProd.eq.Eye
import Lemma.Matrix.SwapMatrix.eq.Eye
import Lemma.Set.In_Range.is.Any_Eq
open Matrix Set
set_option maxHeartbeats 999999


private lemma ofFn_snoc
  {α : Type*} {m : ℕ} (f : Fin (m + 1) → α) :
  List.ofFn f = List.ofFn (fun i : Fin m => f i.castSucc) ++ [f (Fin.last m)] := by
  refine List.ext_getElem (by simp [List.length_ofFn]) ?_
  intro i h1 h2
  simp only [List.getElem_append, List.length_ofFn, List.getElem_ofFn]
  if hi : i < m then
    simp [hi]
  else
    have hi' : i < m + 1 := by simpa [List.length_ofFn] using h1
    have : i = m := Nat.eq_of_lt_succ_of_not_lt hi' hi
    simp [this, Fin.last]

@[path]
private lemma main
  [Semiring α] [CharZero α]
  {n : ℕ}
  {P : Set (Fin n → α)}
-- given
  (hn : n ≥ 2)
  (hP : P = {p | Set.range p = Set.range (fun i : Fin n => ((i : ℕ) : α))}) :
-- imply
  ∀ p ∈ P, ∃ b : Fin n → Fin n,
    p = (fun i : Fin n => (i : α)) ᵥ*
      (List.ofFn fun i : Fin n => swapMatrix (α := α) i (b i)).prod := by
-- proof
  rw [hP]
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  refine (show ∀ m, m ≥ 2 → ∀ (p : Fin m → α),
      Set.range p = Set.range (fun i : Fin m => ((i : ℕ) : α)) →
        ∃ b : Fin m → Fin m,
          p = (fun i : Fin m => (i : α)) ᵥ*
            (List.ofFn fun i : Fin m => swapMatrix (α := α) i (b i)).prod from ?_) n hn p hp
  intro m hm
  induction m, hm using Nat.le_induction with
    | base =>
      intro p hp
      have hR : Set.range (fun i : Fin 2 => ((i : ℕ) : α)) = {(0 : α), (1 : α)} := by
        ext x
        constructor
        ·
          intro hx
          obtain ⟨i, hi⟩ := hx
          fin_cases i <;> aesop
        ·
          intro hx
          simp at hx
          obtain h | h := hx <;> aesop
      have hp' := hp.trans hR
      have mem_pair (j : Fin 2) : p j = (0 : α) ∨ p j = (1 : α) := by
        apply (Set.mem_insert_iff.mp _).elim Or.inl fun h => Or.inr (Set.mem_singleton_iff.mp h)
        erw [← hp']
        exact ⟨j, rfl⟩
      have h01 : (0 : α) ≠ (1 : α) := zero_ne_one
      if h0 : p (0 : Fin 2) = (0 : α) then
        refine ⟨fun i => i, ?_⟩
        rw [MatProd.eq.Eye (α := α) 2, Matrix.vecMul_one]
        apply funext
        intro k
        fin_cases k
        ·
          simpa using h0
        ·
          obtain h1 | h1 := mem_pair (1 : Fin 2)
          ·
            have hr : Set.range p = {(0 : α)} := by
              ext x
              constructor
              ·
                intro hx
                obtain ⟨j, hj⟩ := hx
                fin_cases j <;> grind
              ·
                intro hx
                exact ⟨(0 : Fin 2), h0.trans (Set.mem_singleton_iff.1 hx).symm⟩
            apply (h01 (Set.mem_singleton_iff.1 _).symm).elim
            apply (hr.symm.trans hp').symm ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
          ·
            simpa using h1
      else
        have h0' : p (0 : Fin 2) = (1 : α) := by
          obtain (h | h) := mem_pair (0 : Fin 2) <;> aesop
        refine ⟨fun _ => (0 : Fin 2), ?_⟩
        have hprod : (List.ofFn fun i : Fin 2 => swapMatrix (α := α) i (0 : Fin 2)).prod =
            swapMatrix (α := α) (1 : Fin 2) (0 : Fin 2) := by
          simp [List.ofFn_succ, List.ofFn_zero, SwapMatrix.eq.Eye (α := α)]
        rw [hprod, GetDot_SwapMatrix.eq.Get]
        apply funext
        intro k
        simp only [Function.comp_apply]
        fin_cases k
        ·
          simpa [Equiv.swap_apply_def] using h0'
        ·
          obtain (h1 | h1) := mem_pair (1 : Fin 2)
          ·
            simpa [Equiv.swap_apply_def] using h1
          ·
            have hr' : {(1 : α)} = Set.range p := by
              ext x
              constructor
              ·
                intro hx
                exact ⟨(0 : Fin 2), h0'.trans (Set.mem_singleton_iff.1 hx).symm⟩
              ·
                intro hx
                obtain ⟨j, hj⟩ := hx
                fin_cases j <;> grind
            apply (h01 (Set.mem_singleton_iff.1 _)).elim
            apply (hr'.trans hp').symm ▸ Set.mem_insert _ _
    | succ n hn ih =>
      intro p hp
      obtain ⟨j, hj⟩ := Set.Any_Eq.of.In_Range
        (hp.symm ▸ Set.In_Range.of.Any_Eq (a := (n : α)) ⟨Fin.last n, by simp [Fin.val_last]⟩)
      let W := swapMatrix (α := α) (Fin.last n) j
      let p' : Fin (n + 1) → α := p ∘ Equiv.swap (Fin.last n) j
      have hp'_vec : p' = p ᵥ* W := by
        rw [GetDot_SwapMatrix.eq.Get]
      have hplast : p' (Fin.last n) = (n : α) := by
        simp only [p', Function.comp_apply, Equiv.swap_apply_left, hj]
      have hp'range : Set.range p' = Set.range (fun i : Fin (n + 1) => ((i : ℕ) : α)) := by
        apply Eq.trans _ hp
        ext x
        constructor
        ·
          intro hx
          obtain ⟨t, ht⟩ := hx
          refine ⟨Equiv.swap (Fin.last n) j t, ?_⟩
          simpa [p'] using ht
        ·
          intro hx
          obtain ⟨t, ht⟩ := hx
          refine ⟨Equiv.swap (Fin.last n) j t, ?_⟩
          simp only [p', Function.comp_apply, Equiv.swap_apply_self, ht]
      let q : Fin n → α := fun i => p' i.castSucc
      have hp_inj : Function.Injective p := by
        intro a b hab
        let σ : Fin (n + 1) → Fin (n + 1) := fun i =>
          have : ∃ j : Fin (n + 1), ((j : ℕ) : α) = p i := by
            have : p i ∈ Set.range (fun j : Fin (n + 1) => ((j : ℕ) : α)) := by
              rw [← hp]
              exact ⟨i, rfl⟩
            simpa [Set.mem_range]
          Classical.choose this
        have hσ : ∀ i, ((σ i : ℕ) : α) = p i := fun i =>
          have : ∃ j : Fin (n + 1), ((j : ℕ) : α) = p i := by
            have : p i ∈ Set.range (fun j : Fin (n + 1) => ((j : ℕ) : α)) := by
              rw [← hp]
              exact ⟨i, rfl⟩
            simpa [Set.mem_range]
          Classical.choose_spec this
        apply (Finite.injective_iff_surjective (f := σ)).2 _
          (Fin.ext (Nat.cast_injective ((hσ a).trans (hab.trans (hσ b).symm))))
        intro k
        have : ((k : ℕ) : α) ∈ Set.range p := by
          rw [hp]
          exact ⟨k, rfl⟩
        obtain ⟨i, hi⟩ := this
        refine ⟨i, ?_⟩
        apply Fin.ext (Nat.cast_injective ((hσ i).trans hi))
      have hq : Set.range q = Set.range (fun i : Fin n => ((i : ℕ) : α)) := by
        ext x
        constructor
        ·
          intro hx
          obtain ⟨i, rfl⟩ := hx
          have hmem : q i ∈ Set.range (fun t : Fin (n + 1) => ((t : ℕ) : α)) := by
            rw [← hp'range]
            exact ⟨i.castSucc, rfl⟩
          obtain ⟨t, ht⟩ := hmem
          have ht_ne : t ≠ Fin.last n := by
            intro ht_eq
            have hp'_inj : Function.Injective p' := by
              intro a b hab
              apply (Equiv.swap (Fin.last n) j).injective
              apply hp_inj
              simpa [p'] using hab
            apply (Fin.castSucc_lt_last i).ne
            ·
              apply hp'_inj
              apply Eq.trans _ hplast.symm
              apply ht.symm.trans
              rw [ht_eq]
              simp [Fin.val_last]
          obtain ⟨t0, rfl⟩ := Fin.eq_castSucc_of_ne_last ht_ne
          refine ⟨t0, ?_⟩
          apply (show ((t0 : ℕ) : α) = (((t0.castSucc) : ℕ) : α) by simp [Fin.val_castSucc]).trans ht
        ·
          intro hx
          obtain ⟨i, rfl⟩ := hx
          have hmem : ((i : ℕ) : α) ∈ Set.range p' := by
            rw [hp'range]
            exact ⟨i.castSucc, by simp⟩
          obtain ⟨t, ht⟩ := hmem
          have ht_ne : t ≠ Fin.last n := by
            intro ht_eq
            apply (Nat.ne_of_lt i.isLt)
            apply Nat.cast_injective
              (ht.symm.trans ((congrArg p' ht_eq).trans hplast))
          obtain ⟨t0, rfl⟩ := Fin.eq_castSucc_of_ne_last ht_ne
          refine ⟨t0, ht⟩
      obtain ⟨b0, hb0⟩ := ih q hq
      let b : Fin (n + 1) → Fin (n + 1) :=
        Fin.append (fun i : Fin n => (b0 i).castSucc) (fun _ : Fin 1 => j)
      refine ⟨b, ?_⟩
      have hp_recover : p = p' ᵥ* W := by
        rw [hp'_vec, EqDotDot_SwapMatrix]
      have hb_last : b (Fin.last n) = j := by
        change Fin.append (fun i : Fin n => (b0 i).castSucc) (fun _ : Fin 1 => j)
          (Fin.natAdd n (0 : Fin 1)) = j
        rw [Fin.append_right]
      have hb_cast : ∀ i : Fin n, b i.castSucc = (b0 i).castSucc := by
        intro i
        change Fin.append (fun i : Fin n => (b0 i).castSucc) (fun _ : Fin 1 => j)
          (Fin.castAdd 1 i) = (b0 i).castSucc
        rw [Fin.append_left]
      have hprod :
        (List.ofFn fun i : Fin (n + 1) => swapMatrix (α := α) i (b i)).prod =
          (List.ofFn fun i : Fin n => swapMatrix (α := α) i.castSucc (b0 i).castSucc).prod * W := by
        rw [ofFn_snoc (fun i => swapMatrix (α := α) i (b i)), List.prod_append, List.prod_singleton, hb_last]
        congr 1
        refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
        rw [hb_cast]
      let Me := (List.ofFn fun i : Fin n => swapMatrix (α := α) i.castSucc (b0 i).castSucc).prod
      let M0 := (List.ofFn fun i : Fin n => swapMatrix (α := α) i (b0 i)).prod
      -- #3: Me = fromBlocks M0 0 0 1 reindexed by finSumFinEquiv
      have hMe :
        Me =
          (fromBlocks M0 0 0 (1 : Matrix (Fin 1) (Fin 1) α)).reindex
            finSumFinEquiv finSumFinEquiv := by
        have h :=
          AppendHstackS.eq.MatProd_SwapMatrix.of.Le (α := α) (le_refl n) b0
        have hcast (i : Fin n) : Fin.castLE (le_refl n) i = i := Fin.ext rfl
        have hL :
          (List.ofFn fun i : Fin n =>
              swapMatrix (α := α) (Fin.castLE (le_refl n) i) (b0 i)).prod =
            M0 := by
          refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
          rw [hcast]
        have hR :
          (List.ofFn fun i : Fin n =>
              swapMatrix (α := α)
                (Fin.castAdd 1 (Fin.castLE (le_refl n) i))
                (Fin.castAdd 1 (b0 i))).prod =
            Me := by
          refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
          rw [hcast]
          rfl
        rw [← hR, ← h, hL]
      have embed_vecMul :
        (fun i : Fin (n + 1) => (i : α)) ᵥ* Me =
          fun t : Fin (n + 1) =>
            if h : t = Fin.last n then (n : α)
            else ((fun i : Fin n => (i : α)) ᵥ* M0) (t.castPred h) := by
        rw [hMe, reindex_apply, submatrix_vecMul_equiv]
        simp only [Equiv.symm_symm]
        have hs :
          (fun i : Fin (n + 1) => (i : α)) ∘ finSumFinEquiv =
            Sum.elim (fun i : Fin n => (i : α)) (fun _ : Fin 1 => (n : α)) := by
          funext x
          cases x with
          | inl i =>
            simp [finSumFinEquiv_apply_left, Fin.val_castAdd]
          | inr i =>
            have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
            subst hi
            simp [finSumFinEquiv_apply_right, Fin.val_natAdd]
        rw [hs, vecMul_fromBlocks]
        simp only [vecMul_zero, add_zero, zero_add, vecMul_one, Sum.elim_comp_inl,
          Sum.elim_comp_inr]
        funext t
        rcases ht : finSumFinEquiv.symm t with t0 | t0
        ·
          have ht' : t = t0.castSucc := by
            rw [← Equiv.apply_symm_apply finSumFinEquiv t, ht, finSumFinEquiv_apply_left]
            rfl
          rw [ht'] at ht ⊢
          simp only [Function.comp_apply, ht, Sum.elim_inl, Fin.castSucc_ne_last, ↓reduceDIte,
            Fin.castPred_castSucc]
        ·
          have hi : t0 = 0 := Fin.ext (by have := t0.isLt; omega)
          subst hi
          have ht' : t = Fin.last n := by
            rw [← Equiv.apply_symm_apply finSumFinEquiv t, ht, finSumFinEquiv_apply_right]
            rfl
          rw [ht'] at ht ⊢
          simp only [Function.comp_apply, ht, Sum.elim_inr, ↓reduceDIte]
      have hp'_factor : p' = (fun i : Fin (n + 1) => (i : α)) ᵥ* Me := by
        rw [embed_vecMul]
        funext t
        if ht : t = Fin.last n then
          simp [ht, hplast]
        else
          obtain ⟨t0, rfl⟩ := Fin.eq_castSucc_of_ne_last ht
          simp only [Fin.castSucc_ne_last, ↓reduceDIte, Fin.castPred_castSucc]
          change p' t0.castSucc = ((fun i : Fin n => (i : α)) ᵥ* M0) t0
          rw [← hb0]
      calc
        _ = p' ᵥ* W := hp_recover
        _ = ((fun i : Fin (n + 1) => (i : α)) ᵥ* Me) ᵥ* W := by rw [hp'_factor]
        _ = (fun i : Fin (n + 1) => (i : α)) ᵥ* (Me * W) := by rw [Matrix.vecMul_vecMul]
        _ = (fun i : Fin (n + 1) => (i : α)) ᵥ*
            (List.ofFn fun i : Fin (n + 1) => swapMatrix (α := α) i (b i)).prod := by rw [← hprod]


-- created on 2026-10-31
