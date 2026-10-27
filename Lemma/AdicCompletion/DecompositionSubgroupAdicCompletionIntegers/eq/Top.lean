import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.NumberField_PlaceDecompositionAction
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp Pointwise


/-- ported from external source -/
@[path]
private lemma main
  [Field E] [Field K] [NumberField K] [Algebra E K]
  {w : HeightOneSpectrum (𝓞 K)} [Finite (NumberField.PlaceDecomp.decomp E K w)] :
-- imply
  (w.adicCompletionIntegers K).decompositionSubgroup (FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)) = ⊤ := by
-- proof
  classical
    rw [eq_top_iff]
    intro f _
    obtain ⟨σ, rfl⟩ := FixedPoints.toAlgAut_surjective (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K) f
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
    show (MulSemiringAction.toAlgAut (NumberField.PlaceDecomp.decomp E K w)
        (FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)) (w.adicCompletion K) σ⁻¹) x ∈
      w.adicCompletionIntegers K ↔ x ∈ w.adicCompletionIntegers K
    rw [MulSemiringAction.toAlgAut_apply, MulSemiringAction.toAlgEquiv_apply]
    exact NumberField.PlaceDecomp.smul_mem_adicCompletionIntegers_iff σ⁻¹ x


-- created on 2026-10-23
