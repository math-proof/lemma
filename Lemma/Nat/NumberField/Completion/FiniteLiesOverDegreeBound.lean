import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.NumberTheory.NumberField.Completion.FiniteLiesOverDegreeBound
open scoped NumberField NumberField.LiesOver TensorProduct Valued
open IsDedekindDomain.HeightOneSpectrum


namespace IsDedekindDomain.HeightOneSpectrum

/--
[finrank_adicCompletion_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverDegreeBound.lean)
-/
@[path]
lemma finrank_adicCompletion_le
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
-- imply
  Module.finrank (v.adicCompletion K) (w.adicCompletion L) ≤
    Module.finrank K L := by
-- proof
  let Φ : v.adicCompletion K ⊗[K] L →ₗ[v.adicCompletion K]
    w.adicCompletion L :=
    (Algebra.TensorProduct.lift
      (Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
        (w.adicCompletion L))
      (Algebra.algHom K L (w.adicCompletion L))
      (fun _ _ => mul_comm ..)).toLinearMap
  have h_dense : DenseRange Φ := by
    apply (w.denseRange_algebraMap L).mono
    rintro _ ⟨l, rfl⟩
    exact ⟨1 ⊗ₜ l, by simp [Φ, Algebra.algHom]⟩
  have h_surjective : Function.Surjective Φ := by
    rw [← Set.range_eq_univ, ← Φ.coe_range,
      ← Φ.range.closed_of_finiteDimensional.closure_eq]
    exact h_dense.closure_range
  calc
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) ≤
      Module.finrank (v.adicCompletion K)
        (v.adicCompletion K ⊗[K] L) :=
      LinearMap.finrank_le_finrank_of_surjective h_surjective
    _ = Module.finrank K L := Module.finrank_baseChange

end IsDedekindDomain.HeightOneSpectrum


-- created on 2026-10-20
-- updated on 2026-10-26
