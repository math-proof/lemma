import Initialize.Tactic.Attr.Basic
import Mathlib

open scoped Polynomial

/--
[AdicCompletion_isReduced_and_isSeparable_genericFibre_of_isInvariant](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_isReduced_and_isSeparable_genericFibre_of_isInvariant.lean)
(`BDescN3.isSeparable_pi`)
-/
@[path]
private lemma main
  [Field K]
  [Finite ι]
  (A : ι → Type*)
  [∀ i, Field (A i)]
  [∀ i, Algebra K (A i)]
  [∀ i, Algebra.IsSeparable K (A i)] :
-- imply
  Algebra.IsSeparable K (∀ i, A i) := by
-- proof
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun x => ?_⟩
  let f : ι → K[X] := fun i => minpoly K (x i)
  let s : Finset K[X] := Finset.univ.image f
  let g : K[X] := ∏ p ∈ s, p
  have hmem : ∀ p ∈ s, ∃ i, p = minpoly K (x i) := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨i, rfl⟩
  have hirr : ∀ p ∈ s, Irreducible p := by
    intro p hp
    obtain ⟨i, rfl⟩ := hmem p hp
    exact minpoly.irreducible (Algebra.IsSeparable.isIntegral K (x i))
  have hmonic : ∀ p ∈ s, p.Monic := by
    intro p hp
    obtain ⟨i, rfl⟩ := hmem p hp
    exact minpoly.monic (Algebra.IsSeparable.isIntegral K (x i))
  have hsep : ∀ p ∈ s, p.Separable := by
    intro p hp
    obtain ⟨i, rfl⟩ := hmem p hp
    exact Algebra.IsSeparable.isSeparable K (x i)
  have hg : g.Separable := by
    apply Polynomial.separable_prod'
    ·
      intro p hp q hq hpq
      rw [(hirr p hp).coprime_iff_not_dvd]
      intro hdvd
      exact hpq (Polynomial.eq_of_monic_of_associated (hmonic p hp) (hmonic q hq)
        ((hirr p hp).associated_of_dvd (hirr q hq) hdvd))
    ·
      exact hsep
  have hg0 : Polynomial.aeval x g = 0 := by
    funext i
    have h1 : (Polynomial.aeval x g) i = Polynomial.aeval (x i) g :=
      (Polynomial.aeval_algHom_apply (Pi.evalAlgHom K A i) x g).symm
    rw [h1, Pi.zero_apply]
    apply Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero
    ·
      exact Finset.dvd_prod_of_mem _ (Finset.mem_image_of_mem f (Finset.mem_univ i))
    ·
      exact minpoly.aeval K (x i)
  show (minpoly K x).Separable
  exact Polynomial.Separable.of_dvd hg (minpoly.dvd K x hg0)


-- created on 2026-10-10
