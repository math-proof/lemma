import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial


universe u v

private lemma aeval_mem_adjoin
  {k : Type u} {E : Type v} [Field k] [Field E] [Algebra k E]
  (y : E)
  (c : k[X]) :
    Polynomial.aeval y c ∈ IntermediateField.adjoin k ({y} : Set E) := by
  refine IntermediateField.algebra_adjoin_le_adjoin k _ ?_
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨c, rfl⟩
private lemma linearIndependent_algebraAdjoin
  {k : Type u} {E : Type v} [Field k] [Field E] [Algebra k E] {n : ℕ}
  (y : E) (s : Fin n → E)
    (hind : ∀ c : Fin n → k[X], ∑ i, Polynomial.aeval y (c i) * s i = 0 → c = 0) :
    LinearIndependent (Algebra.adjoin k ({y} : Set E)) s := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  have hg : ∀ i, ∃ p : k[X], Polynomial.aeval y p = (g i : E) := fun i => by
    have h : (g i : E) ∈ (Polynomial.aeval (R := k) y).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      apply (g i).2
    refine (AlgHom.mem_range _).1 h
  choose p hp using hg
  have hsum' : ∑ i, Polynomial.aeval y (p i) * s i = 0 := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hp i, Subalgebra.smul_def, smul_eq_mul]
  have := congrFun (hind p hsum') i
  apply Subtype.ext
  rw [← hp i, this]
  simp
open scoped IntermediateField.algebraAdjoinAdjoin in
private lemma linearIndependent_adjoin
  {k : Type u} {E : Type v} [Field k] [Field E] [Algebra k E] {n : ℕ}
  (y : E) (s : Fin n → E)
    (hind : ∀ c : Fin n → k[X], ∑ i, Polynomial.aeval y (c i) * s i = 0 → c = 0) :
    LinearIndependent (IntermediateField.adjoin k ({y} : Set E)) s :=
  (LinearIndependent.iff_fractionRing (Algebra.adjoin k ({y} : Set E))
    (IntermediateField.adjoin k ({y} : Set E))).mp (linearIndependent_algebraAdjoin y s hind)
private lemma mul_mem_span
  {k : Type u} {E : Type v} [Field k] [Field E] [Algebra k E] {n : ℕ}
  (y : E) (s : Fin n → E)
    (hmul : ∀ i j, ∃ c : Fin n → k[X], s i * s j = ∑ l, Polynomial.aeval y (c l) * s l)
    {a b : E}
    (ha : a ∈ Submodule.span (IntermediateField.adjoin k ({y} : Set E)) (Set.range s))
    (hb : b ∈ Submodule.span (IntermediateField.adjoin k ({y} : Set E)) (Set.range s)) :
    a * b ∈ Submodule.span (IntermediateField.adjoin k ({y} : Set E)) (Set.range s) := by
  set K₀ := IntermediateField.adjoin k ({y} : Set E)
  obtain ⟨α, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K₀).mp ha
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K₀).mp hb
  rw [Finset.sum_mul]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have : α i • s i * (β j • s j) = (α i * β j) • (s i * s j) := by
    simp only [IntermediateField.smul_def, smul_eq_mul, IntermediateField.coe_mul]
    ring
  rw [this]
  refine Submodule.smul_mem _ _ ?_
  obtain ⟨c, hc⟩ := hmul i j
  rw [hc]
  refine Submodule.sum_mem _ fun l _ => ?_
  have : Polynomial.aeval y (c l) * s l = (⟨Polynomial.aeval y (c l), aeval_mem_adjoin y (c l)⟩ : K₀) • s l := by
    rw [IntermediateField.smul_def, smul_eq_mul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
private lemma span_eq_top
  {k : Type u} {E : Type v} [Field k] [Field E] [Algebra k E] {n : ℕ}
  (y : E) (s : Fin n → E)
    (hmul : ∀ i j, ∃ c : Fin n → k[X], s i * s j = ∑ l, Polynomial.aeval y (c l) * s l)
    (hfrac : ∀ z : E, ∃ cu cv : Fin n → k[X],
      ∑ i, Polynomial.aeval y (cv i) * s i ≠ 0 ∧
        z * ∑ i, Polynomial.aeval y (cv i) * s i = ∑ i, Polynomial.aeval y (cu i) * s i) :
    Submodule.span (IntermediateField.adjoin k ({y} : Set E)) (Set.range s) = ⊤ := by
  set K₀ := IntermediateField.adjoin k ({y} : Set E)
  set W : Submodule K₀ E := Submodule.span K₀ (Set.range s) with hW
  have hpolyW : ∀ c : Fin n → k[X], ∑ i, Polynomial.aeval y (c i) * s i ∈ W := by
    intro c
    refine Submodule.sum_mem _ fun i _ => ?_
    have : Polynomial.aeval y (c i) * s i = (⟨Polynomial.aeval y (c i), aeval_mem_adjoin y (c i)⟩ : K₀) • s i := by
      rw [IntermediateField.smul_def, smul_eq_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let _ : FiniteDimensional K₀ W := FiniteDimensional.span_of_finite K₀ (Set.finite_range s)
  have hsurj : ∀ v ∈ W, v ≠ 0 → ∀ w ∈ W, ∃ t ∈ W, v * t = w := by
    intro v hv hv0 w hw
    let φ : W →ₗ[K₀] W :=
      { toFun := fun t => ⟨v * t, mul_mem_span y s hmul hv t.2⟩
        map_add' := fun a b => by
          apply Subtype.ext
          simp [mul_add]
        map_smul' := fun c a => by
          apply Subtype.ext
          simp [IntermediateField.smul_def, smul_eq_mul, mul_left_comm] }
    have hinj : Function.Injective φ := by
      intro a b hab
      have : v * (a : E) = v * (b : E) := congrArg (fun z : W => (z : E)) hab
      exact Subtype.ext (mul_left_cancel₀ hv0 this)
    have hs : Function.Surjective φ := LinearMap.surjective_of_injective hinj
    obtain ⟨t, ht⟩ := hs ⟨w, hw⟩
    exact ⟨t, t.2, congrArg (fun z : W => (z : E)) ht⟩
  rw [eq_top_iff]
  rintro z -
  obtain ⟨cu, cv, hv0, hz⟩ := hfrac z
  set u := ∑ i, Polynomial.aeval y (cu i) * s i
  set v := ∑ i, Polynomial.aeval y (cv i) * s i
  have hu : u ∈ W := hpolyW cu
  have hv : v ∈ W := hpolyW cv
  obtain ⟨t₁, ht₁, hvt₁⟩ := hsurj v hv hv0 v hv
  have h1 : t₁ = 1 := by
    have : v * t₁ = v * 1 := by rw [hvt₁, mul_one]
    exact mul_left_cancel₀ hv0 this
  obtain ⟨t, ht, hvt⟩ := hsurj v hv hv0 t₁ ht₁
  rw [h1] at hvt
  have htinv : t = v⁻¹ := by
    have := congrArg (fun w => v⁻¹ * w) hvt
    simp only [← mul_assoc, inv_mul_cancel₀ hv0, one_mul, mul_one] at this
    exact this
  have hz' : z = u * t := by
    rw [htinv]
    field_simp
    exact hz
  rw [hz']
  exact mul_mem_span y s hmul hu ht

/--
[AlgebraicCurve_finrank_adjoin_eq_card_of_mul_mem_span_of_fractions](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_finrank_adjoin_eq_card_of_mul_mem_span_of_fractions.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k]
  {E : Type v} [Field E] [Algebra k E]
  {n : ℕ}
  (y : E) (s : Fin n → E)
-- given
  (hmul : ∀ i j, ∃ c : Fin n → k[X], s i * s j = ∑ l, Polynomial.aeval y (c l) * s l)
  (hind : ∀ c : Fin n → k[X], ∑ i, Polynomial.aeval y (c i) * s i = 0 → c = 0)
  (hfrac : ∀ z : E, ∃ cu cv : Fin n → k[X],
    ∑ i, Polynomial.aeval y (cv i) * s i ≠ 0 ∧
      z * ∑ i, Polynomial.aeval y (cv i) * s i = ∑ i, Polynomial.aeval y (cu i) * s i) :
-- imply
  FiniteDimensional (IntermediateField.adjoin k ({y} : Set E)) E ∧
    Module.finrank (IntermediateField.adjoin k ({y} : Set E)) E = n := by
-- proof
  have hli := linearIndependent_adjoin y s hind
  have hsp := span_eq_top y s hmul hfrac
  let b : Module.Basis (Fin n) (IntermediateField.adjoin k ({y} : Set E)) E :=
    Module.Basis.mk hli (le_of_eq hsp.symm)
  apply And.intro (Module.Finite.of_basis b) (by rw [Module.finrank_eq_card_basis b, Fintype.card_fin])


-- created on 2026-10-20
