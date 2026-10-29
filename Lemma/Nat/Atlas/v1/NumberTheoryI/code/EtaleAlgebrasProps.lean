import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.NumberTheoryI.code.EtaleAlgebrasProps
open EtaleAlgebra
open scoped Classical


namespace EtaleAlgebra

/--
[pi_single_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean)
-/
@[path]
lemma pi_single_mul
  [DecidableEq ι]
  {F : ι → Type*}
  [∀ i, CommMonoidWithZero (F i)]
  {i : ι}
  {a : F i}
-- given
  (f : ∀ j, F j) :
-- imply
  Pi.single i a * f = Pi.single i (a * f i) := by
-- proof
  ext j; simp only [Pi.mul_apply]
  by_cases h : j = i
  · subst h; simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

end EtaleAlgebra

namespace EtaleAlgebra

/--
[pi_field_not_domain_of_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean)
-/
@[path]
lemma pi_field_not_domain_of_two
  {F : ι → Type*}
  [∀ i, Field (F i)]
  [DecidableEq ι]
  {i j : ι}
-- given
  (hij : i ≠ j) :
-- imply
  ¬ NoZeroDivisors (∀ k, F k) := by
-- proof
  intro h
  have h1 : Pi.single i (1 : F i) ≠ (0 : ∀ k, F k) := by
    intro heq; have := congr_fun heq i; simp [Pi.single_eq_same] at this
  have h2 : Pi.single j (1 : F j) ≠ (0 : ∀ k, F k) := by
    intro heq; have := congr_fun heq j; simp [Pi.single_eq_same] at this
  have h3 : Pi.single i (1 : F i) * Pi.single j (1 : F j) = (0 : ∀ k, F k) := by
    ext k; simp only [Pi.mul_apply, Pi.zero_apply]
    by_cases hki : k = i
    · subst hki; simp [Pi.single_eq_same, Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne hki]
  exact (h.eq_zero_or_eq_zero_of_mul_eq_zero h3).elim h1 h2

end EtaleAlgebra

namespace EtaleAlgebra

/--
[piRestr_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean)
-/
@[path]
lemma piRestr_surjective
  {ι : Type*}
  [Field K]
  [Fintype ι]
  [DecidableEq ι]
  {F : ι → Type*}
  [∀ i, Field (F i)]
  [∀ i, Algebra K (F i)]
  {S : Finset ι} :
-- imply
  Function.Surjective (piRestr (K := K) (F := F) S) := by
-- proof
  intro f; use fun i => if h : i ∈ S then f ⟨i, h⟩ else 0
  ext ⟨i, hi⟩; dsimp [piRestr]; rw [dif_pos hi]

end EtaleAlgebra

namespace EtaleAlgebra

/--
[mem_ker_piRestr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean)
-/
@[path]
lemma mem_ker_piRestr
  {ι : Type*}
  [Field K]
  [Fintype ι]
  [DecidableEq ι]
  {F : ι → Type*}
  [∀ i, Field (F i)]
  [∀ i, Algebra K (F i)]
  {S : Finset ι}
-- given
  (f : ∀ i, F i) :
-- imply
  f ∈ RingHom.ker (piRestr (K := K) (F := F) S) ↔ ∀ i ∈ S, f i = 0 := by
-- proof
  constructor
  · intro hf i hi; exact congr_fun hf ⟨i, hi⟩
  · intro hf; ext ⟨i, hi⟩; exact hf i hi

end EtaleAlgebra

namespace EtaleAlgebra

/--
[ker_phi_eq_ker_piRestr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean)
-/
@[path]
lemma ker_phi_eq_ker_piRestr
  {ι : Type*}
  [Field K]
  [Fintype ι]
  [DecidableEq ι]
  {F : ι → Type*}
  [∀ i, Field (F i)]
  [∀ i, Algebra K (F i)]
  [CommRing B]
  [Algebra K B]
-- given
  (φ : (∀ i, F i) →ₐ[K] B) :
-- imply
  let T := Finset.univ.filter (fun i => ∃ f ∈ RingHom.ker φ, f i ≠ 0) RingHom.ker φ = RingHom.ker (piRestr (K := K) (F := F) (Finset.univ \ T)) := by
-- proof
  intro T; ext f; rw [mem_ker_piRestr]; constructor
  · intro hf i hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, T,
      Finset.mem_filter, not_exists] at hi
    push Not at hi; exact hi f hf
  · intro hf
    suffices h : ∀ i ∉ T, f i = 0 by
      have decomp : f = ∑ j ∈ T, Pi.single j (1 : F j) * f := by
        conv_lhs => rw [← Finset.univ_sum_single f]
        simp_rw [show ∀ i, Pi.single i (f i) = Pi.single i (1 : F i) * f from
          fun i => by rw [pi_single_mul, one_mul]]
        symm; apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hj; rw [pi_single_mul, one_mul, h j hj, Pi.single_zero]
      rw [decomp]; apply Ideal.sum_mem; intro j hj
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨g, hg, hgi⟩ := hj
      have ej_mem : Pi.single j (1 : F j) ∈ RingHom.ker φ := by
        have : Pi.single j (g j)⁻¹ * g ∈ RingHom.ker φ := Ideal.mul_mem_left _ _ hg
        rwa [pi_single_mul, inv_mul_cancel₀ hgi] at this
      exact Ideal.mul_mem_right _ _ ej_mem
    exact fun i hi => hf i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)

end EtaleAlgebra

namespace EtaleAlgebra

/--
[surj_algHom_pi_fields_isSubproduct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean)
-/
@[path]
lemma surj_algHom_pi_fields_isSubproduct
  {ι : Type*}
  [Field K]
  [Fintype ι]
  [DecidableEq ι]
  {F : ι → Type*}
  [∀ i, Field (F i)]
  [∀ i, Algebra K (F i)]
  [CommRing B]
  [Algebra K B]
-- given
  (φ : (∀ i, F i) →ₐ[K] B)
  (hφ : Function.Surjective φ) :
-- imply
  ∃ S : Finset ι, Nonempty (B ≃ₐ[K] ∀ i : S, F i) := by
-- proof
  let T := Finset.univ.filter (fun i => ∃ f ∈ RingHom.ker φ, f i ≠ 0)
  exact ⟨Finset.univ \ T,
    ⟨algEquivOfSurjSameKer φ (piRestr (Finset.univ \ T)) hφ
      (piRestr_surjective _) (ker_phi_eq_ker_piRestr φ)⟩⟩

end EtaleAlgebra

namespace EtaleAlgebra

/--
[algEquiv_field_of_pi_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean)
-/
@[path]
lemma algEquiv_field_of_pi_field
  [Field K]
  [Fintype ι]
  [DecidableEq ι]
  {F : ι → Type*}
  [∀ i, Field (F i)]
  [∀ i, Algebra K (F i)]
  [Field E]
  [Algebra K E]
-- given
  (e : E ≃ₐ[K] ∀ i, F i) :
-- imply
  ∃ j : ι, Nonempty (E ≃ₐ[K] F j) := by
-- proof
  have hne : Nonempty ι := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    exact one_ne_zero (e.injective (funext (IsEmpty.elim hemp)))
  have hnd : NoZeroDivisors (∀ i, F i) := by
    constructor; intro a b hab; by_contra hc; push Not at hc
    obtain ⟨ha0, hb0⟩ := hc
    have hea : e.symm a ≠ 0 := fun h => ha0 (e.symm.injective (by simp [h]))
    have heb : e.symm b ≠ 0 := fun h => hb0 (e.symm.injective (by simp [h]))
    have : e.symm a * e.symm b ≠ 0 := by
      intro h; exact absurd (mul_eq_zero.mp h) (by push Not; exact ⟨hea, heb⟩)
    rw [show e.symm a * e.symm b = e.symm (a * b) from by simp, hab, map_zero] at this
    exact this rfl
  have hsing : ∀ i j : ι, i = j := by
    intro i j; by_contra hij; exact pi_field_not_domain_of_two hij hnd
  obtain ⟨j⟩ := hne
  exact ⟨j, ⟨e.trans (piSingletonAlgEquiv j (hsing · j))⟩⟩

end EtaleAlgebra

namespace EtaleAlgebra

/--
[surjection_to_field_factors](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean)
-/
@[path]
lemma surjection_to_field_factors
  [Field K]
  [Fintype ι]
  [DecidableEq ι]
  {F : ι → Type*}
  [∀ i, Field (F i)]
  [∀ i, Algebra K (F i)]
  [Field E]
  [Algebra K E]
-- given
  (φ : (∀ i, F i) →ₐ[K] E)
  (hφ : Function.Surjective φ) :
-- imply
  ∃ j : ι, Nonempty (E ≃ₐ[K] F j) := by
-- proof
  obtain ⟨S, ⟨e⟩⟩ := surj_algHom_pi_fields_isSubproduct φ hφ
  obtain ⟨⟨j, _⟩, ⟨iso⟩⟩ := algEquiv_field_of_pi_field e
  exact ⟨j, ⟨iso⟩⟩

end EtaleAlgebra

namespace EtaleAlgebra

/--
[etale_decomposition_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean)
-/
@[path]
lemma etale_decomposition_unique
  [Field K]
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {F : ι → Type*}
  [∀ i, Field (F i)]
  [∀ i, Algebra K (F i)]
  {G : κ → Type*}
  [∀ j, Field (G j)]
  [∀ j, Algebra K (G j)]
-- given
  (e : (∀ i, F i) ≃ₐ[K] ∀ j, G j) :
-- imply
  (∀ i, ∃ j, Nonempty (F i ≃ₐ[K] G j)) ∧ (∀ j, ∃ i, Nonempty (G j ≃ₐ[K] F i)) := by
-- proof
  constructor
  · intro i
    have hsurj : Function.Surjective ((Pi.evalAlgHom K F i).comp e.symm.toAlgHom) := by
      intro x
      obtain ⟨y, hy⟩ := e.symm.surjective (Pi.single i x)
      exact ⟨y, by simp [hy, Pi.evalAlgHom_apply, Pi.single_eq_same]⟩
    exact surjection_to_field_factors _ hsurj
  · intro j
    have hsurj : Function.Surjective ((Pi.evalAlgHom K G j).comp e.toAlgHom) := by
      intro x
      obtain ⟨y, hy⟩ := e.surjective (Pi.single j x)
      exact ⟨y, by simp [hy, Pi.evalAlgHom_apply, Pi.single_eq_same]⟩
    exact surjection_to_field_factors _ hsurj

end EtaleAlgebra

/--
[piRestr_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean)
-/
@[path]
private lemma piRestr_apply_eq
  {ι : Type*}
  [Field K]
  [Fintype ι]
  [DecidableEq ι]
  {F : ι → Type*}
  [∀ i, Field (F i)]
  [∀ i, Algebra K (F i)]
  {S : Finset ι}
  {j : S}
-- given
  (f : ∀ i, F i) :
-- imply
  piRestr (K := K) S f j = f j := by
-- proof
  apply EtaleAlgebra.piRestr_apply S f j


-- created on 2026-10-23
-- updated on 2026-10-29
