/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/FieldTheory/Galois/AdditiveHilbert90.lean -/


import Mathlib.GroupTheory.SpecificGroups.Cyclic
import sympy.atlas.FieldTheory.Galois.AdditiveHilbert90
import Lemma.Int.Galois.AdditiveHilbert90


/-!
# Tests for additive Hilbert 90 of a cyclic Galois extension

Compile-time checks for `Algebra.ker_trace_eq_range_algEquiv_sub_id` and
`Algebra.exists_algEquiv_sub_eq_of_trace_eq_zero`: the exact trace-zero iff (with the
reverse direction proved directly from trace invariance rather than the corollary), direct
use of the pointwise corollary, and generator choice under an `IsCyclic` hypothesis.
-/

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L]

namespace MathlibExtTest.FieldTheory.Galois.AdditiveHilbert90

-- The submodule equality gives the exact iff; the reverse direction uses trace invariance
-- directly rather than the corollary.
example (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (x : L) :
    Algebra.trace K L x = 0 ↔ ∃ y : L, σ y - y = x := by
  constructor
  · intro hx
    have hmem : x ∈ LinearMap.ker (Algebra.trace K L) := LinearMap.mem_ker.mpr hx
    rw [Algebra.ker_trace_eq_range_algEquiv_sub_id σ hσ] at hmem
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hmem
    exact ⟨y, by
      simpa only [LinearMap.sub_apply, AlgEquiv.toLinearMap_apply, LinearMap.id_apply]
        using hy⟩
  · rintro ⟨y, rfl⟩
    rw [map_sub, Algebra.trace_eq_of_algEquiv, sub_self]

-- The pointwise corollary applies directly in the generator setting.
example (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {x : L}
    (hx : Algebra.trace K L x = 0) : ∃ y : L, σ y - y = x :=
  Algebra.exists_algEquiv_sub_eq_of_trace_eq_zero σ hσ hx

-- Under a cyclicity hypothesis, a generator exists and both results apply to it.
example [IsCyclic (L ≃ₐ[K] L)] (x : L) (hx : Algebra.trace K L x = 0) :
    ∃ σ : L ≃ₐ[K] L, ∃ y : L, σ y - y = x := by
  obtain ⟨σ, hσ⟩ :
      ∃ σ : L ≃ₐ[K] L, ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ :=
    IsCyclic.exists_generator
  exact ⟨σ, Algebra.exists_algEquiv_sub_eq_of_trace_eq_zero σ hσ hx⟩

-- The equality itself is available at a cyclic generator.
example [IsCyclic (L ≃ₐ[K] L)] :
    ∃ σ : L ≃ₐ[K] L, LinearMap.ker (Algebra.trace K L) =
      LinearMap.range (σ.toLinearMap - LinearMap.id) := by
  obtain ⟨σ, hσ⟩ :
      ∃ σ : L ≃ₐ[K] L, ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ :=
    IsCyclic.exists_generator
  exact ⟨σ, Algebra.ker_trace_eq_range_algEquiv_sub_id σ hσ⟩

end MathlibExtTest.FieldTheory.Galois.AdditiveHilbert90
