import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma not_mem_primeIdealOf_iff {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V) {x : X} (hx : x ∈ V)
    (r : Γ(X, V)) : r ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal ↔ x ∈ X.basicOpen r := by
  rw [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec]
  rfl
/--
[AlgebraicGeometry_exists_isAffineOpen_subset_of_finite_of_isAffine](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_isAffineOpen_subset_of_finite_of_isAffine.lean)
-/
@[path]
private lemma main
    {X : Scheme.{u}} [IsAffine X] (V : X.Opens) (F : Set V.toScheme) (hF : F.Finite) :
    ∃ W : (V.toScheme).Opens, IsAffineOpen W ∧ F ⊆ (W : Set V.toScheme) := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · exact ⟨⊥, isAffineOpen_bot _, Set.empty_subset _⟩
  have hT : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  have key : ∀ (x : X) (r : Γ(X, ⊤)),
      r ∉ (hT.primeIdealOf ⟨x, trivial⟩).asIdeal ↔ x ∈ X.basicOpen r :=
    fun x r => not_mem_primeIdealOf_iff hT trivial r
  have hg : ∀ v : V.toScheme, ∃ r : Γ(X, ⊤), X.basicOpen r ≤ V ∧ v.1 ∈ X.basicOpen r :=
    fun v => hT.exists_basicOpen_le ⟨v.1, v.2⟩ trivial
  choose g hgV hgv using hg
  let I : Ideal Γ(X, ⊤) := Ideal.span (Set.range g)
  have hIV : ∀ r ∈ I, X.basicOpen r ≤ V := by
    intro r hr x hx
    by_contra hxV
    have : I ≤ (hT.primeIdealOf ⟨x, trivial⟩).asIdeal := by
      apply Ideal.span_le.mpr
      rintro _ ⟨v, rfl⟩
      by_contra h
      exact hxV (hgV v ((key x (g v)).mp h))
    exact (key x r).mpr hx (this hr)
  have havoid : ¬ ((I : Set Γ(X, ⊤)) ⊆ ⋃ v ∈ (hF.toFinset : Set V.toScheme),
      ((hT.primeIdealOf ⟨v.1, trivial⟩).asIdeal : Set Γ(X, ⊤))) := by
    rw [Ideal.subset_union_prime v₀ v₀ (fun v _ _ _ => (hT.primeIdealOf ⟨v.1, trivial⟩).isPrime)]
    rintro ⟨v, -, hle⟩
    exact (key v.1 (g v)).mpr (hgv v) (hle (Ideal.subset_span ⟨v, rfl⟩))
  rw [Set.not_subset] at havoid
  obtain ⟨r, hrI, hr⟩ := havoid
  refine ⟨V.ι ⁻¹ᵁ X.basicOpen r, ?_, ?_⟩
  · rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_eq_right.mpr (hIV r hrI)]
    exact hT.basicOpen r
  · intro v hv
    show V.ι v ∈ X.basicOpen r
    rw [Scheme.Opens.ι_apply]
    exact (key v.1 r).mp (fun h => hr (Set.mem_biUnion (Finset.mem_coe.mpr (hF.mem_toFinset.mpr hv)) h))

-- created on 2026-10-20
