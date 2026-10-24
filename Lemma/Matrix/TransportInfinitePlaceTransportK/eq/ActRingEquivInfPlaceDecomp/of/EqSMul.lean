import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_NumberField_ArchimedeanIdeleModule
import Lemma.Definitions.Def_NumberField_InfinitePlaceTransport


/-- ported from external source -/
@[path]
private lemma main
  [Field E] [Field K] [Algebra E K]
  {w : NumberField.InfinitePlace K}
  {σ : NumberField.InfPlaceDecomp.decomp E K w}
-- given
  (h : (σ : K ≃ₐ[E] K) • w = w) :
-- imply
  NumberField.InfinitePlaceTransport.transport (σ : K ≃ₐ[E] K) h = NumberField.InfPlaceDecomp.actRingEquiv σ :=
-- proof
  rfl


-- created on 2026-10-23
