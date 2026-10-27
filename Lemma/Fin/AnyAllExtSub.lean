import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma sum_eq_add_sum_ne
  [Fintype E] [DecidableEq E]
  (e₀ : E)
  (f : E → ℤ) :
  -- imply
  ∑ e, f e = f e₀ + ∑ e : {e // e ≠ e₀}, f e.1 :=
  Fintype.sum_eq_add_sum_subtype_ne f e₀

section

variable {V : Type*} [Fintype V] [DecidableEq V]

private noncomputable def IsFlow
  [Fintype E]
  (src tgt : E → V)
  (ε : E → ℤ) :
  Prop :=
  ∀ i : V, (∑ e, if src e = i then ε e else 0) = (∑ e, if tgt e = i then ε e else 0)

private lemma sum_mul_comp_eq
  [Fintype E]
  (v : E → V)
  (ψ : V → ℤ)
  (ε : E → ℤ) :
  -- imply
  ∑ e, ε e * ψ (v e) = ∑ i, ψ i * ∑ e, (if v e = i then ε e else 0) := by
  -- proof
  have h : ∀ e, ε e * ψ (v e) = ∑ i, (if v e = i then ε e * ψ i else 0) := by
    intro e
    rw [Finset.sum_ite_eq]
    simp
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> ring

private lemma sum_mul_coboundary_eq_zero
  [Fintype E]
  (src tgt : E → V)
  (ψ : V → ℤ)
  (ε : E → ℤ)
  -- given
  (hε : IsFlow src tgt ε) :
  -- imply
  ∑ e, ε e * (ψ (tgt e) - ψ (src e)) = 0 := by
  -- proof
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, sum_mul_comp_eq tgt ψ ε, sum_mul_comp_eq src ψ ε]
  rw [Finset.sum_congr rfl fun i _ => by rw [← hε i], sub_self]

private lemma helper_main :
  -- imply
  ∀ (k : ℕ) (E : Type*) [Fintype E] [DecidableEq E], Fintype.card E = k → ∀ (src tgt : E → V) (q : ℤ) (τ : E → ℤ), (∀ ε : E → ℤ, IsFlow src tgt ε → (∑ e, ε e * τ e) ≡ 0 [ZMOD q]) → ∃ φ : V → ℤ, ∀ e : E, τ e ≡ φ (tgt e) - φ (src e) [ZMOD q] := by
  -- proof
  intro k
  induction k
  ·
    intro E _ _ hcard _ _ _ _ _
    refine ⟨fun _ => 0, fun e => ?_⟩
    apply False.elim ((Iff.mp Fintype.card_eq_zero_iff hcard).false e)
  ·
    rename_i k ih
    intro E _ _ hcard src tgt q τ hτ
    have hne : Nonempty E := Iff.mp Fintype.card_pos_iff (by omega)
    obtain ⟨e₀⟩ := hne
    set a := src e₀ with ha
    set b := tgt e₀ with hb
    let E' := {e // e ≠ e₀}
    have hcard' : Fintype.card E' = k := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      omega
    if hab : a = b then
      have hloop : IsFlow src tgt (fun e => if e = e₀ then 1 else 0) := by
        intro i
        have h1 : ∀ (v : E → V), (∑ e, if v e = i then (if e = e₀ then (1 : ℤ) else 0) else 0) = if v e₀ = i then 1 else 0 := by
          intro v
          rw [show (∑ e, if v e = i then (if e = e₀ then (1 : ℤ) else 0) else 0) = ∑ e, if e = e₀ then (if v e₀ = i then 1 else 0) else 0 from
            Finset.sum_congr rfl fun e _ => by if he : e = e₀ then simp [he] else simp [he]]
          rw [Finset.sum_ite_eq']
          simp
        rw [h1 src, h1 tgt, show src e₀ = a from rfl, show tgt e₀ = b from rfl, hab]
      have hτ0 : τ e₀ ≡ 0 [ZMOD q] := by
        have := hτ _ hloop
        have hsum : (∑ e, (if e = e₀ then (1 : ℤ) else 0) * τ e) = τ e₀ := by
          rw [show (∑ e, (if e = e₀ then (1 : ℤ) else 0) * τ e) = ∑ e, if e = e₀ then τ e else 0 from
            Finset.sum_congr rfl fun e _ => by split_ifs <;> simp, Finset.sum_ite_eq']
          simp
        rwa [hsum] at this
      have hflowE' : ∀ ε' : E' → ℤ, IsFlow (fun e => src e.1) (fun e => tgt e.1) ε' → (∑ e, ε' e * τ e.1) ≡ 0 [ZMOD q] := by
        intro ε' hε'
        let ε : E → ℤ := fun e => if h : e = e₀ then 0 else ε' ⟨e, h⟩
        have hεE' : ∀ e : E', ε e.1 = ε' e := fun e => by
          show (if h : e.1 = e₀ then 0 else ε' ⟨e.1, h⟩) = ε' e
          rw [dite_eq_right e.2]
        have hε0 : ε e₀ = 0 := by
          show (if h : e₀ = e₀ then 0 else _) = 0
          rw [dite_eq_left rfl]
        have hflow : IsFlow src tgt ε := by
          intro i
          rw [sum_eq_add_sum_ne e₀, sum_eq_add_sum_ne e₀, hε0]
          simp only [ite_self, hεE']
          apply congrArg _ (hε' i)
        have := hτ ε hflow
        rwa [sum_eq_add_sum_ne e₀, hε0, zero_mul, zero_add,
          show (∑ e : E', ε e.1 * τ e.1) = ∑ e : E', ε' e * τ e.1 from
            Finset.sum_congr rfl fun e _ => by rw [hεE']] at this
      obtain ⟨φ, hφ⟩ := ih E' hcard' (fun e => src e.1) (fun e => tgt e.1) q (fun e => τ e.1) hflowE'
      refine ⟨φ, fun e => ?_⟩
      if he : e = e₀ then
        rw [he]
        show τ e₀ ≡ φ b - φ a [ZMOD q]
        rw [hab, sub_self]
        apply hτ0
      else
        apply hφ ⟨e, he⟩
    else
      let ψ : V → ℤ := fun i => if i = b then τ e₀ else 0
      let τ' : E → ℤ := fun e => τ e - (ψ (tgt e) - ψ (src e))
      have hψa : ψ a = 0 := by
        show (if a = b then τ e₀ else 0) = 0
        rw [ite_eq_right hab]
      have hψb : ψ b = τ e₀ := by
        show (if b = b then τ e₀ else 0) = τ e₀
        rw [ite_eq_left rfl]
      have hτ'0 : τ' e₀ = 0 := by
        show τ e₀ - (ψ (tgt e₀) - ψ (src e₀)) = 0
        rw [show tgt e₀ = b from rfl, show src e₀ = a from rfl, hψa, hψb]
        ring
      have hτ' : ∀ ε : E → ℤ, IsFlow src tgt ε → (∑ e, ε e * τ' e) ≡ 0 [ZMOD q] := by
        intro ε hε
        have : (∑ e, ε e * τ' e) = (∑ e, ε e * τ e) - ∑ e, ε e * (ψ (tgt e) - ψ (src e)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl fun e _ => by
            show ε e * (τ e - _) = _
            ring
        rw [this, sum_mul_coboundary_eq_zero src tgt ψ ε hε, sub_zero]
        apply hτ ε hε
      let π : V → V := fun i => if i = b then a else i
      have hπa : π a = a := by
        show (if a = b then a else a) = a
        split_ifs <;> rfl
      have hπb : π b = a := by
        show (if b = b then a else b) = a
        rw [ite_eq_left rfl]
      have hπ_of_ne : ∀ {x i : V}, i ≠ a → i ≠ b → (π x = i ↔ x = i) := by
        intro x i hi hib
        show ((if x = b then a else x) = i ↔ x = i)
        if hx : x = b then
          rw [hx, ite_eq_left rfl]
          refine ⟨fun h => (hi h.symm).elim, fun h => (hib h.symm).elim⟩
        else
          rw [ite_eq_right hx]
          apply Iff.rfl
      have hflowE' : ∀ ε' : E' → ℤ, IsFlow (fun e => π (src e.1)) (fun e => π (tgt e.1)) ε' → (∑ e, ε' e * τ' e.1) ≡ 0 [ZMOD q] := by
        intro ε' hε'
        let Sb : (E → V) → ℤ := fun v => ∑ e : E', if v e.1 = b then ε' e else 0
        let Sa : (E → V) → ℤ := fun v => ∑ e : E', if v e.1 = a then ε' e else 0
        let ε : E → ℤ := fun e => if h : e = e₀ then Sb src - Sb tgt else ε' ⟨e, h⟩
        have hεE' : ∀ e : E', ε e.1 = ε' e := fun e => by
          show (if h : e.1 = e₀ then Sb src - Sb tgt else ε' ⟨e.1, h⟩) = ε' e
          rw [dite_eq_right e.2]
        have hε0 : ε e₀ = Sb src - Sb tgt := by
          show (if h : e₀ = e₀ then Sb src - Sb tgt else _) = _
          rw [dite_eq_left rfl]
        have hcontr : ∀ v : E → V, (∑ e : E', if π (v e.1) = a then ε' e else 0) = Sa v + Sb v := by
          intro v
          show _ = (∑ e : E', if v e.1 = a then ε' e else 0) + ∑ e : E', if v e.1 = b then ε' e else 0
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun e _ => ?_
          show (if (if v e.1 = b then a else v e.1) = a then ε' e else 0) = _
          if h1 : v e.1 = b then
            rw [ite_eq_left h1, ite_eq_left rfl, ite_eq_right (fun h2 => hab (h2.symm.trans h1)), ite_eq_left h1, zero_add]
          else
            rw [ite_eq_right h1, ite_eq_right h1, add_zero]
        have hab' : Sa src + Sb src = Sa tgt + Sb tgt := by
          rw [← hcontr src, ← hcontr tgt]
          apply hε' a
        have hflow : IsFlow src tgt ε := by
          intro i
          rw [sum_eq_add_sum_ne e₀, sum_eq_add_sum_ne e₀, hε0]
          simp only [hεE']
          rw [show src e₀ = a from rfl, show tgt e₀ = b from rfl]
          if hib : i = b then
            subst hib
            rw [ite_eq_right hab, ite_eq_left rfl, zero_add]
            show Sb src = Sb src - Sb tgt + Sb tgt
            ring
          else
            if hia : i = a then
              subst hia
              rw [ite_eq_left rfl, ite_eq_right (fun h => hib h.symm)]
              show Sb src - Sb tgt + Sa src = 0 + Sa tgt
              linarith [hab']
            else
              rw [ite_eq_right (fun h => hia h.symm), ite_eq_right (fun h => hib h.symm), zero_add, zero_add]
              have := hε' i
              simp only [hπ_of_ne hia hib] at this
              apply this
        have := hτ' ε hflow
        rwa [sum_eq_add_sum_ne e₀, hτ'0, mul_zero, zero_add,
          show (∑ e : E', ε e.1 * τ' e.1) = ∑ e : E', ε' e * τ' e.1 from
            Finset.sum_congr rfl fun e _ => by rw [hεE']] at this
      obtain ⟨φ', hφ'⟩ := ih E' hcard' (fun e => π (src e.1)) (fun e => π (tgt e.1)) q (fun e => τ' e.1) hflowE'
      refine ⟨fun i => φ' (π i) + ψ i, fun e => ?_⟩
      if he : e = e₀ then
        rw [he]
        show τ e₀ ≡ (φ' (π b) + ψ b) - (φ' (π a) + ψ a) [ZMOD q]
        rw [hπa, hπb, hψa, hψb]
        have : φ' a + τ e₀ - (φ' a + 0) = τ e₀ := by ring
        rw [this]
      else
        have h1 : τ' e ≡ φ' (π (tgt e)) - φ' (π (src e)) [ZMOD q] := hφ' ⟨e, he⟩
        have h2 : τ e = τ' e + (ψ (tgt e) - ψ (src e)) := by
          show τ e = τ e - _ + _
          ring
        show τ e ≡ (φ' (π (tgt e)) + ψ (tgt e)) - (φ' (π (src e)) + ψ (src e)) [ZMOD q]
        have hdiff : φ' (π (tgt e)) + ψ (tgt e) - (φ' (π (src e)) + ψ (src e)) =
          φ' (π (tgt e)) - φ' (π (src e)) + (ψ (tgt e) - ψ (src e)) := by ring
        rw [h2, hdiff]
        apply h1.add_right _
end

/--
[Fin_exists_forall_sub_sub_modEq_of_forall_flow_sum_mul_modEq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Fin_exists_forall_sub_sub_modEq_of_forall_flow_sum_mul_modEq_zero.lean)
-/
@[path]
private lemma main
  (n m : ℕ)
  (src tgt : Fin m → Fin n)
  (q : ℤ)
  (τ : Fin m → ℤ)
  -- given
  (hτ : ∀ ε : Fin m → ℤ, (∀ i : Fin n, (∑ e, if src e = i then ε e else 0) = (∑ e, if tgt e = i then ε e else 0)) → (∑ e, ε e * τ e) ≡ 0 [ZMOD q]) :
  -- imply
  ∃ φ : Fin n → ℤ, ∀ e : Fin m, τ e ≡ φ (tgt e) - φ (src e) [ZMOD q] := by
  -- proof
  apply helper_main (Fintype.card (Fin m)) (Fin m) rfl src tgt q τ hτ


-- created on 2026-10-20
