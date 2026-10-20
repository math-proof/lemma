import Mathlib
import sympy.Basic
import sympy.atlas.FieldTheory.Galois.AdditiveHilbert90
open Algebra


/--
[ker_trace_eq_range_algEquiv_sub_id](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Galois/AdditiveHilbert90.lean)
-/
@[path]
private lemma ker_trace_eq_range_algEquiv_sub_id_eq
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
-- given
  (σ : L ≃ₐ[K] L)
  (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
-- imply
  LinearMap.ker (Algebra.trace K L) =
    LinearMap.range (σ.toLinearMap - LinearMap.id) := by
-- proof
  apply Algebra.ker_trace_eq_range_algEquiv_sub_id σ hσ

/--
[exists_algEquiv_sub_eq_of_trace_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Galois/AdditiveHilbert90.lean)
-/
@[path]
private lemma exists_algEquiv_sub_eq_of_trace_eq_zero_eq
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {x : L}
-- given
  (σ : L ≃ₐ[K] L)
  (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
  (hx : Algebra.trace K L x = 0) :
-- imply
  ∃ y : L, σ y - y = x := by
-- proof
  apply Algebra.exists_algEquiv_sub_eq_of_trace_eq_zero σ hσ hx


-- created on 2026-10-20
