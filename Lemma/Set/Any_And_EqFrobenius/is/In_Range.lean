import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[WittVector_exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WittVector_exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range.lean)
-/
@[path]
private lemma main
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] :
    ∃ c : ℤ_[p] →+* WittVector p K, Function.Injective c ∧
      ∀ w : WittVector p K, WittVector.frobenius w = w ↔ w ∈ Set.range c := by
  classical
  let _ : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  let ι : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hι : Function.Injective ι := ι.injective
  have hroot : ∀ x : K, x ^ p = x → ∃ a : ZMod p, ι a = x := by
    intro x hx
    set f : Polynomial K := Polynomial.X ^ p - Polynomial.X with hf
    have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K (Fact.out : p.Prime).one_lt
    have hdeg : f.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq K (Fact.out : p.Prime).one_lt
    let S : Finset K := Finset.univ.image ι
    have hScard : S.card = p := by
      rw [Finset.card_image_of_injective _ hι, Finset.card_univ, ZMod.card]
    have hSsub : S ⊆ f.roots.toFinset := by
      intro y hy
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hf0, Polynomial.IsRoot.def, hf, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, ← map_pow, ZMod.pow_card, sub_self]
    have hcard : f.roots.toFinset.card ≤ S.card := by
      rw [hScard, ← hdeg]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' f)
    have heq : S = f.roots.toFinset := Finset.eq_of_subset_of_card_le hSsub hcard
    have hxr : x ∈ f.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hf0, Polynomial.IsRoot.def, hf, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, hx, sub_self]
    rw [← heq] at hxr
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hxr
    exact ⟨a, ha⟩
  let c : ℤ_[p] →+* WittVector p K := (WittVector.map ι).comp (WittVector.equiv p).symm.toRingHom
  have hc : ∀ t, c t = WittVector.map ι ((WittVector.equiv p).symm t) := fun t => rfl
  refine ⟨c, ?_, ?_⟩
  · intro s t hst
    rw [hc, hc] at hst
    apply (WittVector.equiv p).symm.injective
    ext n
    apply hι
    have := congrArg (fun v => v.coeff n) hst
    simpa only [WittVector.map_coeff] using this
  · intro w
    constructor
    · intro hw
      have hcoef : ∀ n, (w.coeff n) ^ p = w.coeff n := fun n => by
        have := congrArg (fun v => v.coeff n) hw
        simpa only [WittVector.coeff_frobenius_charP] using this
      choose a ha using fun n => hroot (w.coeff n) (hcoef n)
      refine ⟨WittVector.equiv p (WittVector.mk p a), ?_⟩
      rw [hc, RingEquiv.symm_apply_apply]
      ext n
      rw [WittVector.map_coeff]
      exact ha n
    · rintro ⟨t, rfl⟩
      rw [hc]
      ext n
      rw [WittVector.coeff_frobenius_charP, WittVector.map_coeff, ← map_pow, ZMod.pow_card]

-- created on 2026-10-20
