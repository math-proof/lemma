import Lemma.Matrix.AppendHstackS.eq.MatProd_SwapMatrix.of.Le
import Lemma.Matrix.EqDotDot_SwapMatrix
import Lemma.Matrix.GetDot_SwapMatrix.eq.Get
import Lemma.Matrix.MatProd.eq.Eye
import Lemma.Matrix.SwapMatrix.eq.Eye
import Lemma.Set.In_Range.is.Any_Eq
import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic
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
  {n : ℕ}
  {P : Set (List.Vector ℂ n)}
-- given
  (hn : n ≥ 2)
  (hP : P = {p | Set.range (fun i : Fin n => p.get i) = Set.range (fun i : Fin n => ((i : ℕ) : ℂ))}) :
-- imply
  ∀ p ∈ P, ∃ b : Fin n → Fin n,
    p.get = (fun i : Fin n => (i : ℂ)) ᵥ*
      (List.ofFn fun i : Fin n => swapMatrix (α := ℂ) i (b i)).prod := by
-- proof
  rw [hP]
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  refine (show ∀ m, m ≥ 2 → ∀ (p : List.Vector ℂ m),
      Set.range (fun i : Fin m => p.get i) = Set.range (fun i : Fin m => ((i : ℕ) : ℂ)) →
        ∃ b : Fin m → Fin m,
          p.get = (fun i : Fin m => (i : ℂ)) ᵥ*
            (List.ofFn fun i : Fin m => swapMatrix (α := ℂ) i (b i)).prod from ?_) n hn p hp
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro p hp
    have hR : Set.range (fun i : Fin 2 => ((i : ℕ) : ℂ)) = {(0 : ℂ), (1 : ℂ)} := by
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
    have mem_pair (j : Fin 2) : p.get j = (0 : ℂ) ∨ p.get j = (1 : ℂ) := by
      apply (Set.mem_insert_iff.mp _).elim Or.inl fun h => Or.inr (Set.mem_singleton_iff.mp h)
      erw [← hp']
      exact ⟨j, rfl⟩
    have h01 : (0 : ℂ) ≠ (1 : ℂ) := by norm_num
    if h0 : p.get (0 : Fin 2) = (0 : ℂ) then
      refine ⟨fun i => i, ?_⟩
      rw [MatProd.eq.Eye (α := ℂ) 2, Matrix.vecMul_one]
      apply funext
      intro k
      fin_cases k
      ·
        simpa using h0
      ·
        obtain h1 | h1 := mem_pair (1 : Fin 2)
        ·
          have hr : Set.range (fun i : Fin 2 => p.get i) = {(0 : ℂ)} := by
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
      have h0' : p.get (0 : Fin 2) = (1 : ℂ) := by
        obtain (h | h) := mem_pair (0 : Fin 2) <;> aesop
      refine ⟨fun _ => (0 : Fin 2), ?_⟩
      have hprod : (List.ofFn fun i : Fin 2 => swapMatrix (α := ℂ) i (0 : Fin 2)).prod =
          swapMatrix (α := ℂ) (1 : Fin 2) (0 : Fin 2) := by
        simp [List.ofFn_succ, List.ofFn_zero, SwapMatrix.eq.Eye (α := ℂ)]
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
          have hr' : {(1 : ℂ)} = Set.range (fun i : Fin 2 => p.get i) := by
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
      (hp.symm ▸ Set.In_Range.of.Any_Eq (a := (n : ℂ)) ⟨Fin.last n, by simp [Fin.val_last]⟩)
    let W := swapMatrix (α := ℂ) (Fin.last n) j
    let p' : List.Vector ℂ (n + 1) := List.Vector.ofFn (p.get ∘ Equiv.swap (Fin.last n) j)
    have hp't : ∀ t : Fin (n + 1), p'.get t = p.get (Equiv.swap (Fin.last n) j t) := by
      intro t
      simp [p', List.Vector.get_ofFn]
    have hp'_vec : p'.get = p.get ᵥ* W := by
      rw [GetDot_SwapMatrix.eq.Get]
      funext t
      simp [p', List.Vector.get_ofFn]
    have hplast : p'.get (Fin.last n) = (n : ℂ) := by
      rw [hp't, Equiv.swap_apply_left, hj]
    have hp'range : Set.range (fun i : Fin (n + 1) => p'.get i) =
        Set.range (fun i : Fin (n + 1) => ((i : ℕ) : ℂ)) := by
      apply Eq.trans _ hp
      ext x
      constructor
      ·
        intro hx
        obtain ⟨t, ht⟩ := hx
        refine ⟨Equiv.swap (Fin.last n) j t, ?_⟩
        apply (hp't t).symm.trans ht
      ·
        intro hx
        obtain ⟨t, ht⟩ := hx
        refine ⟨Equiv.swap (Fin.last n) j t, ?_⟩
        calc
          _ = p.get (Equiv.swap (Fin.last n) j (Equiv.swap (Fin.last n) j t)) := hp't _
          _ = p.get t := by rw [Equiv.swap_apply_self]
          _ = x := ht
    let q : List.Vector ℂ n := List.Vector.ofFn (fun i : Fin n => p'.get i.castSucc)
    have hq_get : ∀ i : Fin n, q.get i = p'.get i.castSucc := by
      intro i
      simp [q, List.Vector.get_ofFn]
    have hp_inj : Function.Injective fun i : Fin (n + 1) => p.get i := by
      intro a b hab
      let σ : Fin (n + 1) → Fin (n + 1) := fun i =>
        have : ∃ j : Fin (n + 1), ((j : ℕ) : ℂ) = p.get i := by
          have : p.get i ∈ Set.range (fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) := by
            rw [← hp]
            exact ⟨i, rfl⟩
          simpa [Set.mem_range]
        Classical.choose this
      have hσ : ∀ i, ((σ i : ℕ) : ℂ) = p.get i := fun i =>
        have : ∃ j : Fin (n + 1), ((j : ℕ) : ℂ) = p.get i := by
          have : p.get i ∈ Set.range (fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) := by
            rw [← hp]
            exact ⟨i, rfl⟩
          simpa [Set.mem_range]
        Classical.choose_spec this
      apply (Finite.injective_iff_surjective (f := σ)).2 _
        (Fin.ext (Nat.cast_injective ((hσ a).trans (hab.trans (hσ b).symm))))
      intro k
      have : ((k : ℕ) : ℂ) ∈ Set.range (fun i : Fin (n + 1) => p.get i) := by
        rw [hp]
        exact ⟨k, rfl⟩
      obtain ⟨i, hi⟩ := this
      refine ⟨i, ?_⟩
      apply Fin.ext (Nat.cast_injective ((hσ i).trans hi))
    have hq : Set.range (fun i : Fin n => q.get i) = Set.range (fun i : Fin n => ((i : ℕ) : ℂ)) := by
      ext x
      constructor
      ·
        intro hx
        obtain ⟨i, rfl⟩ := hx
        have hmem : q.get i ∈ Set.range (fun t : Fin (n + 1) => ((t : ℕ) : ℂ)) := by
          rw [← hp'range]
          exact ⟨i.castSucc, (hq_get i).symm⟩
        obtain ⟨t, ht⟩ := hmem
        have ht_ne : t ≠ Fin.last n := by
          intro ht_eq
          have hp'_inj : Function.Injective fun i : Fin (n + 1) => p'.get i := by
            intro a b hab
            apply (Equiv.swap (Fin.last n) j).injective
            apply hp_inj
            apply ((hp't a).symm.trans hab).trans (hp't b)
          apply (Fin.castSucc_lt_last i).ne
          ·
            apply hp'_inj
            apply Eq.trans _ hplast.symm
            apply (hq_get i).symm.trans
            apply ht.symm.trans
            rw [ht_eq]
            simp [Fin.val_last]
        obtain ⟨t0, rfl⟩ := Fin.eq_castSucc_of_ne_last ht_ne
        refine ⟨t0, ?_⟩
        apply (show ((t0 : ℕ) : ℂ) = (((t0.castSucc) : ℕ) : ℂ) by simp [Fin.val_castSucc]).trans ht
      ·
        intro hx
        obtain ⟨i, rfl⟩ := hx
        have hmem : ((i : ℕ) : ℂ) ∈ Set.range (fun t : Fin (n + 1) => p'.get t) := by
          rw [hp'range]
          exact ⟨i.castSucc, by simp⟩
        obtain ⟨t, ht⟩ := hmem
        have ht_ne : t ≠ Fin.last n := by
          intro ht_eq
          apply (Nat.ne_of_lt i.isLt)
          apply Nat.cast_injective
            (ht.symm.trans ((congrArg p'.get ht_eq).trans hplast))
        obtain ⟨t0, rfl⟩ := Fin.eq_castSucc_of_ne_last ht_ne
        refine ⟨t0, ?_⟩
        apply (hq_get t0).trans ht
    obtain ⟨b0, hb0⟩ := ih q hq
    let b : Fin (n + 1) → Fin (n + 1) :=
      Fin.append (fun i : Fin n => (b0 i).castSucc) (fun _ : Fin 1 => j)
    refine ⟨b, ?_⟩
    have hp_recover : p.get = p'.get ᵥ* W := by
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
      (List.ofFn fun i : Fin (n + 1) => swapMatrix (α := ℂ) i (b i)).prod =
        (List.ofFn fun i : Fin n => swapMatrix (α := ℂ) i.castSucc (b0 i).castSucc).prod * W := by
      rw [ofFn_snoc (fun i => swapMatrix (α := ℂ) i (b i)), List.prod_append, List.prod_singleton,
        hb_last]
      congr 1
      refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
      rw [hb_cast]
    let Me := (List.ofFn fun i : Fin n => swapMatrix (α := ℂ) i.castSucc (b0 i).castSucc).prod
    let M0 := (List.ofFn fun i : Fin n => swapMatrix (α := ℂ) i (b0 i)).prod
    have hMe :
      Me =
        (fromBlocks M0 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).reindex
          finSumFinEquiv finSumFinEquiv := by
      have h :=
        AppendHstackS.eq.MatProd_SwapMatrix.of.Le (α := ℂ) (le_refl n) b0
      have hcast (i : Fin n) : Fin.castLE (le_refl n) i = i := Fin.ext rfl
      have hL :
        (List.ofFn fun i : Fin n =>
            swapMatrix (α := ℂ) (Fin.castLE (le_refl n) i) (b0 i)).prod =
          M0 := by
        refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
        rw [hcast]
      have hR :
        (List.ofFn fun i : Fin n =>
            swapMatrix (α := ℂ)
              (Fin.castAdd 1 (Fin.castLE (le_refl n) i))
              (Fin.castAdd 1 (b0 i))).prod =
          Me := by
        refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
        rw [hcast]
        rfl
      rw [← hR, ← h, hL]
    have embed_vecMul :
      (fun i : Fin (n + 1) => (i : ℂ)) ᵥ* Me =
        fun t : Fin (n + 1) =>
          if h : t = Fin.last n then (n : ℂ)
          else ((fun i : Fin n => (i : ℂ)) ᵥ* M0) (t.castPred h) := by
      rw [hMe, reindex_apply, submatrix_vecMul_equiv]
      simp only [Equiv.symm_symm]
      have hs :
        (fun i : Fin (n + 1) => (i : ℂ)) ∘ finSumFinEquiv =
          Sum.elim (fun i : Fin n => (i : ℂ)) (fun _ : Fin 1 => (n : ℂ)) := by
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
    have hp'_factor : p'.get = (fun i : Fin (n + 1) => (i : ℂ)) ᵥ* Me := by
      rw [embed_vecMul]
      funext t
      if ht : t = Fin.last n then
        simp [ht, hplast]
      else
        obtain ⟨t0, rfl⟩ := Fin.eq_castSucc_of_ne_last ht
        simp only [Fin.castSucc_ne_last, ↓reduceDIte, Fin.castPred_castSucc]
        change p'.get t0.castSucc = ((fun i : Fin n => (i : ℂ)) ᵥ* M0) t0
        rw [← hq_get t0, hb0]
    calc
      _ = p'.get ᵥ* W := hp_recover
      _ = ((fun i : Fin (n + 1) => (i : ℂ)) ᵥ* Me) ᵥ* W := by rw [hp'_factor]
      _ = (fun i : Fin (n + 1) => (i : ℂ)) ᵥ* (Me * W) := by rw [Matrix.vecMul_vecMul]
      _ = (fun i : Fin (n + 1) => (i : ℂ)) ᵥ*
          (List.ofFn fun i : Fin (n + 1) => swapMatrix (α := ℂ) i (b i)).prod := by rw [← hprod]


-- created on 2020-09-01
-- updated on 2026-10-31
