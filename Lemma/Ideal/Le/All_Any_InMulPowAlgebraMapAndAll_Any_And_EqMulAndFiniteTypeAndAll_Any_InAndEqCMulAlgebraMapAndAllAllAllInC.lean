import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private noncomputable def genSet {A K : Type u} [CommRing A] [Field K] [Algebra A K] (C : Subalgebra A K) (J : Ideal ↥C) (t : A) : Set K :=
  {x : K | ∃ i ∈ J, x * algebraMap A K t = ((i : ↥C) : K)}
private lemma mem_genSet {A K : Type u} [CommRing A] [Field K] [Algebra A K] {C : Subalgebra A K} {J : Ideal ↥C} {t : A} {x : K} : x ∈ genSet C J t ↔ ∃ i ∈ J, x * algebraMap A K t = ((i : ↥C) : K) := Iff.rfl
private lemma coe_mem_adjoin {A K : Type u} [CommRing A] [Field K] [Algebra A K] (C : Subalgebra A K) (S : Set K) (c : ↥C) : (c : K) ∈ Algebra.adjoin ↥C S :=
  Subalgebra.algebraMap_mem (Algebra.adjoin ↥C S) c
private lemma exists_pow_mul_mem {A K : Type u} [CommRing A] [Field K] [Algebra A K] (C : Subalgebra A K) (J : Ideal ↥C) (t : A) {b : K} (hb : b ∈ Algebra.adjoin ↥C (genSet C J t)) : ∃ n : ℕ, algebraMap A K t ^ n * b ∈ C := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hb
  ·
    intro x hx
    obtain ⟨i, -, hi⟩ := hx
    refine ⟨1, ?_⟩
    rw [pow_one, mul_comm, hi]
    apply i.2
  ·
    intro c
    refine ⟨0, ?_⟩
    rw [pow_zero, one_mul]
    apply c.2
  ·
    intro x y _ _ hx hy
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have : algebraMap A K t ^ (m + n) * (x + y) = algebraMap A K t ^ n * (algebraMap A K t ^ m * x) + algebraMap A K t ^ m * (algebraMap A K t ^ n * y) := by ring
    rw [this]
    apply add_mem (mul_mem (pow_mem (C.algebraMap_mem t) n) hm) (mul_mem (pow_mem (C.algebraMap_mem t) m) hn)
  ·
    intro x y _ _ hx hy
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have : algebraMap A K t ^ (m + n) * (x * y) = (algebraMap A K t ^ m * x) * (algebraMap A K t ^ n * y) := by ring
    rw [this]
    apply mul_mem hm hn
private lemma div_mem_genSet {A K : Type u} [CommRing A] [Field K] [Algebra A K] {C : Subalgebra A K} {J : Ideal ↥C} {t : A} (ht0 : algebraMap A K t ≠ 0) {i : ↥C} (hi : i ∈ J) : ((i : ↥C) : K) * (algebraMap A K t)⁻¹ ∈ genSet C J t :=
  ⟨i, hi, by rw [mul_assoc, inv_mul_cancel₀ ht0, mul_one]⟩
private lemma adjoin_genSet_eq_adjoin_image {A K : Type u} [CommRing A] [Field K] [Algebra A K] {C : Subalgebra A K} {J : Ideal ↥C} {t : A} (ht0 : algebraMap A K t ≠ 0) (s : Set ↥C) (hs : Ideal.span s = J) : Algebra.adjoin ↥C (genSet C J t) = Algebra.adjoin ↥C ((fun i : ↥C => ((i : ↥C) : K) * (algebraMap A K t)⁻¹) '' s) := by
  apply le_antisymm
  ·
    refine Algebra.adjoin_le ?_
    intro x hx
    obtain ⟨i, hi, hx⟩ := hx
    have hx' : x = ((i : ↥C) : K) * (algebraMap A K t)⁻¹ := by
      rw [← hx, mul_assoc, mul_inv_cancel₀ ht0, mul_one]
    rw [hx']
    rw [← hs] at hi
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hi
    ·
      intro y hy
      exact Algebra.subset_adjoin ⟨y, hy, rfl⟩
    ·
      rw [ZeroMemClass.coe_zero, zero_mul]
      apply zero_mem _
    ·
      intro y z _ _ hy hz
      rw [Subalgebra.coe_add, add_mul]
      apply add_mem hy hz
    ·
      intro c y _ hy
      rw [smul_eq_mul, Subalgebra.coe_mul, mul_assoc]
      have : (c : K) * (((y : ↥C) : K) * (algebraMap A K t)⁻¹) = c • (((y : ↥C) : K) * (algebraMap A K t)⁻¹) := rfl
      rw [this]
      apply Subalgebra.smul_mem _ hy c
  ·
    refine Algebra.adjoin_le ?_
    intro x hx
    obtain ⟨i, hi, rfl⟩ := hx
    apply Algebra.subset_adjoin (div_mem_genSet ht0 (hs ▸ Ideal.subset_span hi))
private lemma finiteType_adjoin_genSet {A K : Type u} [CommRing A] [Field K] [Algebra A K] {C : Subalgebra A K} {J : Ideal ↥C} {t : A} (ht0 : algebraMap A K t ≠ 0) (hJ : J.FG) : Algebra.FiniteType ↥C ↥(Algebra.adjoin ↥C (genSet C J t)) := by
  classical
  obtain ⟨s, hs⟩ := hJ
  rw [adjoin_genSet_eq_adjoin_image ht0 (s : Set ↥C) hs, ← Finset.coe_image]
  apply (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)
/--
[Subalgebra_le_and_exists_pow_mul_mem_and_finiteType_of_eq_restrictScalars_adjoin_div](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Subalgebra_le_and_exists_pow_mul_mem_and_finiteType_of_eq_restrictScalars_adjoin_div.lean)
-/
@[path]
private lemma main
  {A K : Type u} [CommRing A] [Field K] [Algebra A K]
  (C : Subalgebra A K)
  (J : Ideal ↥C)
  (t : A)
  (B : Subalgebra A K)
  -- given
  (ht0 : algebraMap A K t ≠ 0)
  (hB : B = (Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * algebraMap A K t = ((i : ↥C) : K)}).restrictScalars A) :
  -- imply
  C ≤ B ∧ (∀ b : K, b ∈ B → ∃ n : ℕ, algebraMap A K t ^ n * b ∈ C) ∧ ((∀ f : K, ∃ g h : ↥C, (h : K) ≠ 0 ∧ f * (h : K) = (g : K)) → ∀ f : K, ∃ g h : ↥B, (h : K) ≠ 0 ∧ f * (h : K) = (g : K)) ∧ (J.FG → Algebra.FiniteType A ↥C → Algebra.FiniteType A ↥B) ∧ (∀ i : ↥C, i ∈ J → ∃ b : K, b ∈ B ∧ ((i : ↥C) : K) = algebraMap A K t * b) ∧ (∀ Q : Ideal ↥B, algebraMap A ↥B t ∈ Q → ∀ i : ↥C, i ∈ J → ∀ hiB : ((i : ↥C) : K) ∈ B, (⟨((i : ↥C) : K), hiB⟩ : ↥B) ∈ Q) := by
  -- proof
  have hmem : ∀ b : K, b ∈ B ↔ b ∈ Algebra.adjoin ↥C (genSet C J t) := by
    intro b
    rw [hB]
    rfl
  have h1 : C ≤ B := fun c hc => (hmem c).mpr (coe_mem_adjoin C _ ⟨c, hc⟩)
  have h5 : ∀ i : ↥C, i ∈ J → ∃ b : K, b ∈ B ∧ ((i : ↥C) : K) = algebraMap A K t * b := by
    intro i hi
    refine ⟨((i : ↥C) : K) * (algebraMap A K t)⁻¹, (hmem _).mpr (Algebra.subset_adjoin (div_mem_genSet ht0 hi)), ?_⟩
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ ht0, mul_one]
  refine ⟨h1, ?_, ?_, ?_, h5, ?_⟩
  ·
    intro b hb
    apply exists_pow_mul_mem C J t ((hmem b).mp hb)
  ·
    intro hfrac f
    obtain ⟨g, h, hh, hf⟩ := hfrac f
    exact ⟨⟨(g : K), h1 g.2⟩, ⟨(h : K), h1 h.2⟩, hh, hf⟩
  ·
    intro hJ hC
    let _ := hC
    let _ : Algebra.FiniteType ↥C ↥(Algebra.adjoin ↥C (genSet C J t)) := finiteType_adjoin_genSet ht0 hJ
    have hAB' : Algebra.FiniteType A ↥(Algebra.adjoin ↥C (genSet C J t)) := Algebra.FiniteType.trans (S := ↥C) hC inferInstance
    subst hB
    let e : ↥(Algebra.adjoin ↥C (genSet C J t)) →ₐ[A] ↥((Algebra.adjoin ↥C (genSet C J t)).restrictScalars A) :=
      { toFun := fun x => ⟨x.1, x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl
        commutes' := fun _ => rfl }
    exact hAB'.of_surjective e (fun y => ⟨⟨y.1, y.2⟩, rfl⟩)
  ·
    intro Q htQ i hi hiB
    obtain ⟨b, hbB, hib⟩ := h5 i hi
    have : (⟨((i : ↥C) : K), hiB⟩ : ↥B) = algebraMap A ↥B t * ⟨b, hbB⟩ := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
      apply hib
    rw [this]
    apply Ideal.mul_mem_right _ _ htQ


-- created on 2026-10-20
