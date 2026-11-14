import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.GaloisRep_Adic
import Def.FLTPrelim_Ramification
import Lemma.Int.P2MUtil

open GaloisRepAdic

/--
[GaloisRepAdic_ordinaryLine_eq_of_exists_inertia_residual_ne_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_ordinaryLine_eq_of_exists_inertia_residual_ne_one.lean)
-/

private lemma  mem_span_iff_repr_one_eq_zero {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin 2) R V) (v : V) : v ∈ R ∙ b 0 ↔ b.repr v 1 = 0 := by
  constructor
  · intro hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp
  · intro hv
    have := b.sum_repr v
    rw [Fin.sum_univ_two, hv, zero_smul, add_zero] at this
    rw [← this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
@[path]
private lemma main
  [CommRing A] [IsLocalRing A]
  {ρ : GaloisRepAdic A}
  {P : ValuationSubring (AlgebraicClosure ℚ)}
  {L L' : Submodule A ρ.V}
-- given
  (hLb : ∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0)
  (hL'b : ∃ b : Module.Basis (Fin 2) A ρ.V, L' = A ∙ b 0)
  (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L)
  (hL'I : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L')
  (hram : ∃ τ ∈ P.inertiaSubgroupIn ℚ, ρ.residual.ρ τ ≠ 1) :
-- imply
  L = L' := by
-- proof
  obtain ⟨b, rfl⟩ := hLb
  obtain ⟨b', rfl⟩ := hL'b
  obtain ⟨τ, hτI, hτ⟩ := hram

  have hkill : ∀ x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A ρ.V),
      ∀ c : IsLocalRing.ResidueField A,
        TensorProduct.tmul A c x = (0 : TensorProduct A (IsLocalRing.ResidueField A) ρ.V) := by
    intro x hx c
    refine Submodule.smul_induction_on
      (p := fun x => TensorProduct.tmul A c x =
        (0 : TensorProduct A (IsLocalRing.ResidueField A) ρ.V)) hx ?_ ?_
    · intro a ha w _
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
        IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff a).mpr ha,
        zero_mul, TensorProduct.zero_tmul]
    · intro x y hx hy
      rw [TensorProduct.tmul_add, hx, hy, add_zero]
  have hres1 : (∀ u : ρ.V, ρ.ρ τ u - u ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A ρ.V)) →
      ρ.residual.ρ τ = 1 := by
    intro hτm
    refine LinearMap.ext fun w => ?_
    show (ρ.ρ τ).baseChange (IsLocalRing.ResidueField A) w = w
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul c v =>
      rw [LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub]
      exact hkill _ (hτm v) c
    | add x y hx hy => rw [map_add, hx, hy]

  have core : ∀ c c' : Module.Basis (Fin 2) A ρ.V,
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ A ∙ c 0) →
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ A ∙ c' 0) →
      c.repr (c' 0) 1 ≠ 0 → False := by
    intro c c' hcI hc'I hβ
    apply hτ
    apply hres1
    intro u
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hc'I τ hτI u)
    have h1 : c.repr (ρ.ρ τ u - u) 1 = 0 :=
      (mem_span_iff_repr_one_eq_zero c _).mp (hcI τ hτI u)
    rw [← hd, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    have hdm : d ∈ IsLocalRing.maximalIdeal A := by
      by_contra hdu
      have hu : IsUnit d := by
        rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hdu
      apply hβ
      calc c.repr (c' 0) 1 = ((hu.unit⁻¹ : Aˣ) : A) * (d * c.repr (c' 0) 1) := by
            rw [← mul_assoc, hu.val_inv_mul, one_mul]
        _ = 0 := by rw [h1, mul_zero]
    rw [← hd]
    exact Submodule.smul_mem_smul hdm Submodule.mem_top
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem]
    by_contra hmem
    exact core b' b hL'I hLI fun h0 =>
      hmem ((mem_span_iff_repr_one_eq_zero b' _).mpr h0)
  · rw [Submodule.span_singleton_le_iff_mem]
    by_contra hmem
    exact core b b' hLI hL'I fun h0 =>
      hmem ((mem_span_iff_repr_one_eq_zero b _).mpr h0)


-- created on 2026-10-23
