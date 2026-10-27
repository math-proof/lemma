import Mathlib
import Initialize.Tactic.Attr.Basic


noncomputable def limSub
  {R : Type u}
  [CommRing R]
  (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
  (τ : ∀ k, E (k + 1) →ₗ[R] E k) : Submodule R (∀ k, E k) where
  carrier := {e | ∀ k, τ k (e (k + 1)) = e k}
  add_mem' := by
    intro a b ha hb k
    simp only [Pi.add_apply, map_add, ha k, hb k]
  zero_mem' := by
    intro k
    simp
  smul_mem' := by
    intro c a ha k
    simp only [Pi.smul_apply, map_smul, ha k]

private lemma mem_limSub
  {R : Type u}
  [CommRing R]
  {E : ℕ → Type u} [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
  (τ : ∀ k, E (k + 1) →ₗ[R] E k) (e : ∀ k, E k) :
  e ∈ limSub E τ ↔ ∀ k, τ k (e (k + 1)) = e k := Iff.rfl

private lemma apply_eq_zero_of_le
  {R : Type u}
  [CommRing R]
  {E : ℕ → Type u} [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
  (τ : ∀ k, E (k + 1) →ₗ[R] E k) {e : ∀ k, E k} (he : e ∈ limSub E τ) {N j : ℕ} (hj : j ≤ N)
  (hN : e N = 0) : e j = 0 := by
  have key : ∀ i : ℕ, e (j + i) = 0 → e j = 0 := by
    intro i
    induction i with
    | zero => intro h; simpa using h
    | succ i ih =>
      intro h
      apply ih
      have h' : e (j + i + 1) = 0 := h
      rw [← he (j + i), h', map_zero]
  refine key (N - j)
  rw [Nat.add_sub_of_le hj]
  apply hN

private lemma exists_mem_apply_eq
  {R : Type u}
  [CommRing R]
  {E : ℕ → Type u} [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
  (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k)) :
  ∀ (k : ℕ) (x : E k), ∃ e : ∀ j, E j, e ∈ limSub E τ ∧ e k = x := by
  intro k
  induction k with
  | zero =>
    intro x
    let seq : ∀ j, E j := fun j => Nat.rec (motive := fun j => E j) x (fun j y => Classical.choose (hτs j y)) j
    refine ⟨seq, ?_, rfl⟩
    intro j
    exact Classical.choose_spec (hτs j (seq j))
  | succ k ih =>
    intro x
    obtain ⟨e', he', hk⟩ := ih (τ k x)
    let seq : ∀ j, E j := fun j => Nat.rec (motive := fun j => E j) (e' 0)
      (fun j y => if j + 1 ≤ k then e' (j + 1) else if h : j = k then h ▸ x else Classical.choose (hτs j y)) j
    have hseq_le : ∀ j, j ≤ k → seq j = e' j := by
      intro j hj
      cases j with
      | zero => rfl
      | succ j =>
        show (if j + 1 ≤ k then e' (j + 1) else _) = e' (j + 1)
        rw [ite_eq_left hj]
    have hseq_k1 : seq (k + 1) = x := by
      show (if k + 1 ≤ k then e' (k + 1) else if h : k = k then h ▸ x else _) = x
      rw [ite_eq_right (by omega), dite_eq_left rfl]
    have hseq_gt : ∀ j, k < j → seq (j + 1) = Classical.choose (hτs j (seq j)) := by
      intro j hj
      show (if j + 1 ≤ k then e' (j + 1) else if h : j = k then h ▸ x else Classical.choose (hτs j (seq j))) = _
      rw [ite_eq_right (by omega), dite_eq_right (by omega)]
    refine ⟨seq, ?_, hseq_k1⟩
    intro j
    obtain hlt | heq | hgt := lt_trichotomy j k
    ·
      rw [hseq_le (j + 1) (by omega), hseq_le j hlt.le]; exact he' j
    ·
      subst heq
      rw [hseq_k1, hseq_le j le_rfl, hk]
    ·
      rw [hseq_gt j hgt]; exact Classical.choose_spec (hτs j (seq j))

private lemma exists_sum_of_mem_span_smul
  {R : Type u}
  [CommRing R]
  {X : Type u} [AddCommGroup X] [Module R X] {s : ℕ} (g : Fin s → R)
  (N : Submodule R X) {x : X} (hx : x ∈ Submodule.span R (Set.range g) • N) :
  ∃ v : Fin s → X, (∀ i, v i ∈ N) ∧ x = ∑ i, g i • v i := by
  refine Submodule.smul_induction_on
    (p := fun x => ∃ v : Fin s → X, (∀ i, v i ∈ N) ∧ x = ∑ i, g i • v i) hx ?_ ?_
  ·
    intro r hr m hm
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hr
    refine ⟨fun i => c i • m, fun i => N.smul_mem _ hm, ?_⟩
    rw [← hc, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm, mul_smul]
  ·
    intro a b ha hb
    obtain ⟨v, hv, rfl⟩ := ha
    obtain ⟨v', hv', rfl⟩ := hb
    refine ⟨v + v', fun i => N.add_mem (hv i) (hv' i), ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.add_apply, smul_add]
/--
[Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {I : Ideal R}
  {E : ℕ → Type u} [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
-- given
  (hI : I.FG)
  (τ : ∀ k, E (k + 1) →ₗ[R] E k)
  (hτs : ∀ k, Function.Surjective (τ k))
  (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1)))) :
-- imply
  ∃ L : Submodule R (∀ k, E k),
      (∀ e : ∀ k, E k, e ∈ L ↔ ∀ k, τ k (e (k + 1)) = e k) ∧
      (∀ k, Function.Surjective ((LinearMap.proj k).comp L.subtype : L →ₗ[R] E k)) ∧
      (∀ k, LinearMap.ker ((LinearMap.proj k).comp L.subtype : L →ₗ[R] E k) =
        I ^ (k + 1) • (⊤ : Submodule R L)) := by
-- proof
  classical
    refine ⟨limSub E τ, fun e => Iff.rfl, ?_, ?_⟩
    ·
      intro k x
      obtain ⟨e, he, hx⟩ := exists_mem_apply_eq τ hτs k x
      exact ⟨⟨e, he⟩, hx⟩
    ·
      have hp : ∀ (k : ℕ) (l : limSub E τ),
          ((LinearMap.proj k).comp (limSub E τ).subtype : limSub E τ →ₗ[R] E k) l = (l : ∀ j, E j) k :=
        fun k l => rfl
      have hsurjL : ∀ k, Function.Surjective
        ((LinearMap.proj k).comp (limSub E τ).subtype : limSub E τ →ₗ[R] E k) := by
        intro k x
        obtain ⟨e, he, hx⟩ := exists_mem_apply_eq τ hτs k x
        exact ⟨⟨e, he⟩, hx⟩
      have hsup : ∀ (d : ℕ) (w : limSub E τ), w ∈ I ^ (d + 1) • (⊤ : Submodule R (limSub E τ)) →
          (w : ∀ j, E j) d = 0 := by
        intro d w hw
        refine Submodule.smul_induction_on (p := fun w : limSub E τ => (w : ∀ j, E j) d = 0) hw ?_ ?_
        ·
          intro r hr l _
          rw [Submodule.coe_smul, Pi.smul_apply, ← l.2 d, ← map_smul]
          have : r • (l : ∀ j, E j) (d + 1) ∈ LinearMap.ker (τ d) := by
            rw [hτk]; exact Submodule.smul_mem_smul hr Submodule.mem_top
          exact this
        ·
          intro a b ha hb
          rw [Submodule.coe_add, Pi.add_apply, ha, hb, add_zero]
      intro n
      apply le_antisymm
      swap
      ·
        intro w hw
        rw [LinearMap.mem_ker, hp]
        exact hsup n w hw
      intro x hx
      rw [LinearMap.mem_ker, hp] at hx
      obtain ⟨s, g, hg⟩ : ∃ (s : ℕ) (g : Fin s → R), Submodule.span R (Set.range g) = I ^ (n + 1) :=
        Submodule.fg_iff_exists_fin_generating_family.1 hI.pow
      have hgmem : ∀ i, g i ∈ I ^ (n + 1) := fun i => hg ▸ Submodule.subset_span (Set.mem_range_self i)
      have hcomp : ∀ (l : Fin s → limSub E τ) (j : ℕ),
          ((∑ i, g i • l i : limSub E τ) : ∀ j, E j) j = ∑ i, g i • ((l i : ∀ j, E j) j) := by
        intro l j
        rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, Pi.smul_apply]
      have step : ∀ (d : ℕ) (l : Fin s → limSub E τ),
          ((x - ∑ i, g i • l i : limSub E τ) : ∀ j, E j) (n + d + 1) = 0 →
          ∃ l' : Fin s → limSub E τ,
            ((x - ∑ i, g i • l' i : limSub E τ) : ∀ j, E j) (n + d + 1 + 1) = 0 ∧
            ∀ i, ((l' i - l i : limSub E τ) : ∀ j, E j) d = 0 := by
        intro d l hz
        have hz2 : ((x - ∑ i, g i • l i : limSub E τ) : ∀ j, E j) (n + d + 1 + 1) ∈
          Submodule.span R (Set.range g) • (I ^ (d + 1) • (⊤ : Submodule R (E (n + d + 1 + 1)))) := by
          have hmem : ((x - ∑ i, g i • l i : limSub E τ) : ∀ j, E j) (n + d + 1 + 1) ∈ LinearMap.ker (τ (n + d + 1)) := by
            rw [LinearMap.mem_ker, (x - ∑ i, g i • l i).2 (n + d + 1)]; apply hz
          have hpow : I ^ (n + d + 1 + 1) = I ^ (n + 1) * I ^ (d + 1) := by
            rw [← pow_add]; congr 1; omega
          rw [hτk, hpow, Submodule.mul_smul, ← hg] at hmem
          apply hmem
        obtain ⟨v, hv, hzv⟩ := exists_sum_of_mem_span_smul g _ hz2
        have hlift : ∀ i, ∃ w : limSub E τ, w ∈ I ^ (d + 1) • (⊤ : Submodule R (limSub E τ)) ∧
            (w : ∀ j, E j) (n + d + 1 + 1) = v i := by
          intro i
          have hmap : (I ^ (d + 1) • (⊤ : Submodule R (limSub E τ))).map
            ((LinearMap.proj (n + d + 1 + 1)).comp (limSub E τ).subtype) = I ^ (d + 1) • ⊤ := by
            rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 (hsurjL (n + d + 1 + 1))]
          have hvi : v i ∈ (I ^ (d + 1) • (⊤ : Submodule R (limSub E τ))).map
            ((LinearMap.proj (n + d + 1 + 1)).comp (limSub E τ).subtype) := by
            rw [hmap]; exact hv i
          obtain ⟨w, hw, hwv⟩ := hvi
          exact ⟨w, hw, hwv⟩
        choose w hwI hwv using hlift
        refine ⟨l + w, ?_, fun i => ?_⟩
        ·
          have e1 : x - ∑ i, g i • (l + w) i = (x - ∑ i, g i • l i) - ∑ i, g i • w i := by
          simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
          abel
          rw [e1, Submodule.coe_sub, Pi.sub_apply, hzv, hcomp, sub_eq_zero]
          exact Finset.sum_congr rfl fun i _ => by rw [hwv]
        ·
          have e2 : (l + w) i - l i = w i := by simp
          rw [e2]
          exact hsup d (w i) (hwI i)
      have init : ∃ l : Fin s → limSub E τ,
          ((x - ∑ i, g i • l i : limSub E τ) : ∀ j, E j) (n + 0 + 1) = 0 := by
        have hmem : (x : ∀ j, E j) (n + 1) ∈ Submodule.span R (Set.range g) • (⊤ : Submodule R (E (n + 1))) := by
          have : (x : ∀ j, E j) (n + 1) ∈ LinearMap.ker (τ n) := by
            rw [LinearMap.mem_ker, x.2 n]; apply hx
          rw [hτk, ← hg] at this
          apply this
        obtain ⟨v, -, hxv⟩ := exists_sum_of_mem_span_smul g _ hmem
        choose l hl using fun i => hsurjL (n + 1) (v i)
        refine ⟨l, ?_⟩
        rw [show n + 0 + 1 = n + 1 by rfl, Submodule.coe_sub, Pi.sub_apply, hxv, hcomp, sub_eq_zero]
        exact Finset.sum_congr rfl fun i _ => by rw [← hl i]; rfl
      let seqE : ∀ d : ℕ, {l : Fin s → limSub E τ //
          ((x - ∑ i, g i • l i : limSub E τ) : ∀ j, E j) (n + d + 1) = 0} := fun d =>
        Nat.rec (motive := fun d => {l : Fin s → limSub E τ //
          ((x - ∑ i, g i • l i : limSub E τ) : ∀ j, E j) (n + d + 1) = 0})
          ⟨Classical.choose init, Classical.choose_spec init⟩
          (fun d prev => ⟨Classical.choose (step d prev.1 prev.2), (Classical.choose_spec (step d prev.1 prev.2)).1⟩) d
      have hseq : ∀ d, ((x - ∑ i, g i • (seqE d).1 i : limSub E τ) : ∀ j, E j) (n + d + 1) = 0 :=
        fun d => (seqE d).2
      have hdiff : ∀ (d : ℕ) (i : Fin s), (((seqE (d + 1)).1 i - (seqE d).1 i : limSub E τ) : ∀ j, E j) d = 0 :=
        fun d i => (Classical.choose_spec (step d (seqE d).1 (seqE d).2)).2 i
      have hstat : ∀ (i : Fin s) (j d m : ℕ), j ≤ d →
          (((seqE (d + m)).1 i : limSub E τ) : ∀ j, E j) j = (((seqE d).1 i : limSub E τ) : ∀ j, E j) j := by
        intro i j d m hj
        induction m with
        | zero => rfl
        | succ m ih =>
          rw [← ih]
          have h0 := apply_eq_zero_of_le τ ((seqE (d + m + 1)).1 i - (seqE (d + m)).1 i).2
            (show j ≤ d + m by omega) (hdiff (d + m) i)
          rw [Submodule.coe_sub, Pi.sub_apply, sub_eq_zero] at h0
          apply h0
      let Y : Fin s → ∀ j, E j := fun i j => (((seqE j).1 i : limSub E τ) : ∀ j, E j) j
      have hY : ∀ i, Y i ∈ limSub E τ := by
        intro i j
        show τ j ((((seqE (j + 1)).1 i : limSub E τ) : ∀ j, E j) (j + 1)) = (((seqE j).1 i : limSub E τ) : ∀ j, E j) j
        rw [((seqE (j + 1)).1 i).2 j]
        exact hstat i j j 1 le_rfl
      have hxY : x = ∑ i, g i • (⟨Y i, hY i⟩ : limSub E τ) := by
        apply Subtype.ext
        funext j
        have h0 := apply_eq_zero_of_le τ (x - ∑ i, g i • (seqE j).1 i).2 (show j ≤ n + j + 1 by omega) (hseq j)
        rw [Submodule.coe_sub, Pi.sub_apply, sub_eq_zero] at h0
        rw [h0, hcomp, hcomp]
      rw [hxY]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hgmem i) Submodule.mem_top


-- created on 2026-10-23
