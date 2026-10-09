import Mathlib
import sympy.Basic


/--
[AddMonoidHom_natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidHom_natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul.lean)
-/

noncomputable def ρ
  {K : Type*}
  [Field K]
  (p : ℕ)
  [Fact p.Prime]
  [CharP K p]
  [PerfectField K]
  (c : K) : K :=
  (frobeniusEquiv K p).symm c

lemma semi_K
  {K : Type*}
  [Field K]
  {p : ℕ}
  [Fact p.Prime]
  [CharP K p]
  [PerfectField K]
  {F M : Type*} [Field F] [Algebra K F] [AddCommGroup M] [Module F M] [Module K M]
  [IsScalarTower K F M] (C : M →+ M) (hsemi : ∀ (f : F) (m : M), C (f ^ p • m) = f • C m)
  (c : K) (m : M) : C (c • m) = ρ (K := K) p c • C m := by
  have h1 : c • m = (algebraMap K F (ρ (K := K) p c)) ^ p • m := by
    show c • m = (algebraMap K F ((frobeniusEquiv K p).symm c)) ^ p • m
    rw [← map_pow, frobeniusEquiv_symm_pow_p K p c, algebraMap_smul]
  rw [h1, hsemi, algebraMap_smul]

lemma exists_castHom_eq_of_ρ_eq
  {K : Type*}
  [Field K]
  {p : ℕ}
  [Fact p.Prime]
  [CharP K p]
  [PerfectField K]
  (c : K) (hc : ρ (K := K) p c = c) :
    ∃ k : ZMod p, ZMod.castHom (dvd_refl p) K k = c := by
  classical
  have hcp : c ^ p = c := by
    conv_lhs => rw [← hc]
    show (frobeniusEquiv K p).symm c ^ p = c
    apply frobeniusEquiv_symm_pow_p K p c
  let f : Polynomial K := Polynomial.X ^ p - Polynomial.X
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hp1
  have hdeg : f.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq K hp1
  have hroot : ∀ x : K, x ^ p = x → x ∈ f.roots := by
    intro x hx
    rw [Polynomial.mem_roots hf0, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hx, sub_self]
  let ι' : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hinj : Function.Injective ι' := ZMod.castHom_injective K
  have himg : ∀ k : ZMod p, ι' k ∈ f.roots := fun k => hroot _ (by rw [← map_pow, ZMod.pow_card])
  by_contra hne
  push Not at hne
  have hcmem : c ∈ f.roots := hroot c hcp
  have hsub : insert c (Finset.univ.image ι') ⊆ f.roots.toFinset := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rw [Multiset.mem_toFinset]
    obtain rfl | hx := hx
    · exact hcmem
    ·
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
      exact himg k
  have hnotin : c ∉ Finset.univ.image ι' := by
    intro hx
    obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hx
    exact hne k hk
  have hcard1 : (insert c (Finset.univ.image ι')).card = p + 1 := by
    rw [Finset.card_insert_of_notMem hnotin, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      ZMod.card]
  have hcard2 : f.roots.toFinset.card ≤ p := calc _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ = p := hdeg
  have := Finset.card_le_card hsub
  omega

@[path]
private lemma main
  [AddCommGroup G]
  [Field K] [Field F] [Algebra K F] [AddCommGroup M] [Module F M] [Module K M]
  [IsScalarTower K F M] [PerfectField K]
  {p : ℕ} [Fact p.Prime] [CharP K p]
  {W : Submodule K M} [FiniteDimensional K W]
  {C : M →+ M}
  {φ : G →+ M}
-- given
  (hsemi : ∀ (f : F) (m : M), C (f ^ p • m) = f • C m)
  (hφ : Function.Injective φ)
  (hfix : ∀ g : G, C (φ g) = φ g)
  (hW : ∀ g : G, φ g ∈ W) :
-- imply
  Finite G ∧ Nat.card G ≤ p ^ Module.finrank K W := by
-- proof
  classical
  set d := Module.finrank K W with hd

  let instZ : Module (ZMod p) M := Module.compHom M (ZMod.castHom (dvd_refl p) K)
  have hzsmul : ∀ (k : ZMod p) (m : M), (k • m : M) = (ZMod.castHom (dvd_refl p) K k) • m :=
    fun _ _ => rfl
  have ρ_castHom : ∀ k : ZMod p,
      ρ (K := K) p (ZMod.castHom (dvd_refl p) K k) = ZMod.castHom (dvd_refl p) K k := by
    intro k
    show (frobeniusEquiv K p).symm (ZMod.castHom (dvd_refl p) K k) = ZMod.castHom (dvd_refl p) K k
    have hf : frobenius K p (ZMod.castHom (dvd_refl p) K k) = ZMod.castHom (dvd_refl p) K k := by
      rw [frobenius_def, ← map_pow, ZMod.pow_card]
    rw [← hf, frobeniusEquiv_symm_apply_frobenius, hf]

  let U : Submodule (ZMod p) M :=
    { carrier := {m | m ∈ W ∧ C m = m}
      add_mem' := fun {a b} ha hb => ⟨W.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2]⟩
      zero_mem' := ⟨W.zero_mem, by rw [map_zero]⟩
      smul_mem' := fun k {m} hm => by
        refine ⟨?_, ?_⟩
        ·
          rw [hzsmul]
          exact W.smul_mem _ hm.1
        ·
          rw [hzsmul, semi_K (p := p) C hsemi, hm.2, ρ_castHom k] }
  have hUmem : ∀ x : U, (x : M) ∈ W ∧ C (x : M) = (x : M) := fun x => x.2

  have key : ∀ (s : Finset U) (t : Finset s) (c : s → K),
      (∀ i, i ∉ t → c i = 0) → (∑ i, c i • ((i : U) : M)) = 0 → (∃ i, c i ≠ 0) →
      ∃ k : s → ZMod p, (∑ i, k i • (i : U)) = 0 ∧ ∃ i, k i ≠ 0 := by
    intro s t
    induction t using Finset.strongInduction with
    | H t ih =>
      intro c hsupp hrel hne
      obtain ⟨i₀, hi₀⟩ := hne
      have hi₀t : i₀ ∈ t := by
        by_contra h
        exact hi₀ (hsupp i₀ h)

      let c' : s → K := fun i => (c i₀)⁻¹ * c i
      have hc'₀ : c' i₀ = 1 := inv_mul_cancel₀ hi₀
      have hc'supp : ∀ i, i ∉ t → c' i = 0 := fun i hi => by
        show (c i₀)⁻¹ * c i = 0
        rw [hsupp i hi, mul_zero]
      have hc'rel : (∑ i, c' i • ((i : U) : M)) = 0 := by
        have : (∑ i, c' i • ((i : U) : M)) = (c i₀)⁻¹ • ∑ i, c i • ((i : U) : M) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul]
        rw [this, hrel, smul_zero]

      have hCrel : (∑ i, ρ (K := K) p (c' i) • ((i : U) : M)) = 0 := by
        have h := congrArg C hc'rel
        rw [map_zero, map_sum] at h
        rw [← h]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [semi_K (p := p) C hsemi, (hUmem (i : U)).2]

      let c'' : s → K := fun i => c' i - ρ (K := K) p (c' i)
      have hc''rel : (∑ i, c'' i • ((i : U) : M)) = 0 := by
        show (∑ i, (c' i - ρ (K := K) p (c' i)) • ((i : U) : M)) = 0
        simp only [sub_smul, Finset.sum_sub_distrib, hc'rel, hCrel, sub_zero]
      have hc''₀ : c'' i₀ = 0 := by
        show c' i₀ - (frobeniusEquiv K p).symm (c' i₀) = 0
        rw [hc'₀, map_one, sub_self]
      have hc''supp : ∀ i, i ∉ t.erase i₀ → c'' i = 0 := by
        intro i hi
        if hii : i = i₀ then
          rwa [hii]
        else
          have hit : i ∉ t := fun h => hi (Finset.mem_erase.2 ⟨hii, h⟩)
          show c' i - (frobeniusEquiv K p).symm (c' i) = 0
          rw [hc'supp i hit, map_zero, sub_self]
      if hall : ∀ i, c'' i = 0 then
        have hfix' : ∀ i, ∃ k : ZMod p, ZMod.castHom (dvd_refl p) K k = c' i := by
          intro i
          apply exists_castHom_eq_of_ρ_eq (p := p)
          apply Eq.symm
          apply sub_eq_zero.mp
          exact hall i
        choose k hk using hfix'
        refine ⟨k, ?_, ⟨i₀, ?_⟩⟩
        ·
          apply Subtype.ext
          rw [Submodule.coe_sum, Submodule.coe_zero]
          have : ∀ i : s, ((k i • (i : U) : U) : M) = c' i • ((i : U) : M) := fun i => by
            rw [Submodule.coe_smul, hzsmul, hk]
          simp only [this]
          exact hc'rel
        ·
          intro h0
          have h1 := hk i₀
          rw [h0, map_zero, hc'₀] at h1
          exact zero_ne_one h1
      else
        push Not at hall
        exact ih (t.erase i₀) (Finset.erase_ssubset hi₀t) c'' hc''supp hc''rel hall

  have hcardle : ∀ s : Finset U, LinearIndependent (ZMod p) (fun i : s => (i : U)) → s.card ≤ d := by
    intro s hs
    let v : s → W := fun i => ⟨((i : U) : M), (hUmem (i : U)).1⟩
    have hv : LinearIndependent K v := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      by_contra hne
      push Not at hne
      obtain ⟨i, hi⟩ := hne
      have hrel : (∑ i, c i • ((i : U) : M)) = 0 := by
        have h := congrArg (Submodule.subtype W) hc
        rw [map_sum, map_zero] at h
        simpa [v] using h
      obtain ⟨k, hk, j, hj⟩ := key s Finset.univ c (fun i h => absurd (Finset.mem_univ i) h) hrel ⟨i, hi⟩
      exact hj ((Fintype.linearIndependent_iff.1 hs) k hk j)
    have h := hv.fintype_card_le_finrank
    simpa using h
  have hrank : Module.rank (ZMod p) U ≤ d := rank_le hcardle
  have : Module.Finite (ZMod p) U :=
    (Module.rank_lt_aleph0_iff).1 (lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0 (n := d)))
  have hfinrank : Module.finrank (ZMod p) U ≤ d := Module.finrank_le_of_rank_le hrank
  have hcardU : Nat.card U ≤ p ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_eq_fintype_card, ZMod.card]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hfinrank
  have : Finite U := Module.finite_of_finite (ZMod p)

  let ψ : G → U := fun g => ⟨φ g, hW g, hfix g⟩
  have hψ : Function.Injective ψ := fun a b h => hφ (congrArg (fun x : U => (x : M)) h)
  exact ⟨Finite.of_injective ψ hψ, (Nat.card_le_card_of_injective ψ hψ).trans hcardU⟩


-- created on 2026-10-09
