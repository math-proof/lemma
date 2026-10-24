import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.PiFieldDecomposition
open PiFieldQuotient


namespace PiFieldQuotient

/--
[evalAlgHom_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldDecomposition.lean)
-/
@[path]
private lemma evalAlgHom_surjective {K : Type*} [Field K] {ι : Type*}
  {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)] (i : ι) :
  Function.Surjective (Pi.evalAlgHom K F i) := by
  classical
  intro y
  exact ⟨Pi.single i y, by simpa only [Pi.evalAlgHom_apply] using Pi.single_eq_same i y⟩

end PiFieldQuotient

namespace PiFieldQuotient

/--
[exists_factor_of_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldDecomposition.lean)
-/
@[path]
through exactly one coordinate. -/
private lemma exists_factor_of_surjective {K : Type*} [Field K] {ι : Type*}
  [Finite ι] {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  {E : Type*} [Field E] [Algebra K E]
  (φ : (∀ i, F i) →ₐ[K] E) (hφ : Function.Surjective φ) :
  ∃ i : ι, ∃ e : F i ≃ₐ[K] E, ∀ x, e (x i) = φ x := by
  classical
  obtain ⟨S, a, ha⟩ := exists_algEquiv_restrict φ hφ
  have hcoord : ∀ (x : ∀ i, F i) (s : S), a (φ x) s = x (s : ι) := by
    intro x s
    have h := congrArg (fun ψ : (∀ i, F i) →ₐ[K] (∀ s : S, F (s : ι)) => ψ x s) ha
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.pi_apply,
      Pi.evalAlgHom_apply] using h
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have h10 : (1 : ∀ s : S, F (s : ι)) = 0 := by
      ext s
      have hmemEmpty : s.val ∈ (∅ : Finset ι) := by
        rwa [← h]
      exact absurd hmemEmpty (Finset.notMem_empty _)
    have hE : (1 : E) = 0 := by
      have h2 := congrArg (fun y => a.symm y) h10
      simp at h2
    exact one_ne_zero hE
  have hsub : ∀ s₁ s₂ : S, s₁ = s₂ := by
    intro s₁ s₂
    by_contra hne12
    have hne1 : (Pi.single s₁ (1 : F (s₁ : ι)) : ∀ s : S, F (s : ι)) ≠ 0 := by
      intro h
      have h1 := congrArg (fun y : (∀ s : S, F (s : ι)) => y s₁) h
      simp only [Pi.single_eq_same, Pi.zero_apply] at h1
      exact one_ne_zero h1
    have hne2 : (Pi.single s₂ (1 : F (s₂ : ι)) : ∀ s : S, F (s : ι)) ≠ 0 := by
      intro h
      have h1 := congrArg (fun y : (∀ s : S, F (s : ι)) => y s₂) h
      simp only [Pi.single_eq_same, Pi.zero_apply] at h1
      exact one_ne_zero h1
    have hu1 : a.symm (Pi.single s₁ (1 : F (s₁ : ι))) ≠ 0 := by
      intro h
      apply hne1
      have h2 := congrArg ⇑a h
      simpa only [AlgEquiv.apply_symm_apply, map_zero] using h2
    have hu2 : a.symm (Pi.single s₂ (1 : F (s₂ : ι))) ≠ 0 := by
      intro h
      apply hne2
      have h2 := congrArg ⇑a h
      simpa only [AlgEquiv.apply_symm_apply, map_zero] using h2
    have hprod : (Pi.single s₁ (1 : F (s₁ : ι)) * Pi.single s₂ (1 : F (s₂ : ι)) :
      ∀ s : S, F (s : ι)) = 0 := by
      ext t
      by_cases ht : t = s₁
      · subst ht
        simp only [Pi.mul_apply, Pi.single_eq_same,
          Pi.single_eq_of_ne hne12 _, mul_zero, Pi.zero_apply]
      · simp only [Pi.mul_apply, Pi.single_eq_of_ne ht _, zero_mul,
        Pi.zero_apply]
    have hmul : a.symm (Pi.single s₁ (1 : F (s₁ : ι))) *
      a.symm (Pi.single s₂ (1 : F (s₂ : ι))) = 0 := by
      rw [← map_mul, hprod, map_zero]
    exact (mul_ne_zero hu1 hu2) hmul
  obtain ⟨x₀, hx₀⟩ := hne
  let s0 : S := ⟨x₀, hx₀⟩
  refine ⟨s0.val, (a.trans (singletonEquiv S s0 (fun s => hsub s s0))).symm, fun x => ?_⟩
  apply (a.trans (singletonEquiv S s0 (fun s => hsub s s0))).injective
  simp only [AlgEquiv.apply_symm_apply, AlgEquiv.trans_apply]
  exact (hcoord x s0).symm

end PiFieldQuotient

namespace PiFieldQuotient

/--
[exists_indexEquiv_algEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldDecomposition.lean)
-/
@[path]
lemma exists_indexEquiv_algEquiv
  {K : Type u} [Field K]
  {ι : Type v} [Finite ι]
  {κ : Type w} [Finite κ]
  {F : ι → Type x} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  {G : κ → Type y} [∀ j, Field (G j)] [∀ j, Algebra K (G j)]
-- given
  (e : (∀ i, F i) ≃ₐ[K] (∀ j, G j)) :
-- imply
  ∃ σ : ι ≃ κ, ∀ i, Nonempty (F i ≃ₐ[K] G (σ i)) := by
-- proof
  classical
  have he : Function.Surjective (e.toAlgHom) := by
    intro y
    exact ⟨e.symm y, AlgEquiv.apply_symm_apply e y⟩
  have heSymm : Function.Surjective (e.symm.toAlgHom) := by
    intro y
    exact ⟨e y, AlgEquiv.symm_apply_apply e y⟩
  have hf : ∀ j : κ, ∃ i : ι, ∃ ef : F i ≃ₐ[K] G j, ∀ x, ef (x i) = e x j := by
    intro j
    exact exists_factor_of_surjective ((Pi.evalAlgHom K G j).comp e.toAlgHom)
      ((evalAlgHom_surjective (K := K) (F := G) j).comp he)
  have hg : ∀ i : ι, ∃ k : κ, ∃ eg : G k ≃ₐ[K] F i, ∀ y, eg (y k) = e.symm y i := by
    intro i
    exact exists_factor_of_surjective ((Pi.evalAlgHom K F i).comp e.symm.toAlgHom)
      ((evalAlgHom_surjective (K := K) (F := F) i).comp heSymm)
  choose f ef hf' using hf
  choose g eg hg' using hg
  have hgf : ∀ j : κ, g (f j) = j := by
    intro j
    by_contra hne
    have h0 : (Pi.single j (1 : G j)) (g (f j)) = 0 := Pi.single_eq_of_ne hne _
    have h1 : e.symm (Pi.single j (1 : G j)) (f j) = 0 := by
      have h := hg' (f j) (Pi.single j (1 : G j))
      rwa [h0, map_zero] at h
    have h2 := hf' j (e.symm (Pi.single j (1 : G j)))
    rw [AlgEquiv.apply_symm_apply] at h2
    rw [h1, map_zero, Pi.single_eq_same] at h2
    exact zero_ne_one h2
  have hfg : ∀ i : ι, f (g i) = i := by
    intro i
    by_contra hne
    have h0 : (Pi.single i (1 : F i)) (f (g i)) = 0 := Pi.single_eq_of_ne hne _
    have h1 : e (Pi.single i (1 : F i)) (g i) = 0 := by
      have h := hf' (g i) (Pi.single i (1 : F i))
      rwa [h0, map_zero] at h
    have h2 := hg' i (e (Pi.single i (1 : F i)))
    rw [AlgEquiv.symm_apply_apply] at h2
    rw [h1, map_zero, Pi.single_eq_same] at h2
    exact zero_ne_one h2
  exact ⟨Equiv.mk g f (fun i => hfg i) (fun j => hgf j), fun i => ⟨(eg i).symm⟩⟩

end PiFieldQuotient


-- created on 2026-10-20
-- updated on 2026-10-23
