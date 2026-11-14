import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AbsoluteValue.ArchimedeanIdeleModule
import Lemma.AlgEquiv.InfinitePlaceTransport


/-- ported from external source -/
@[path]
private lemma main
  [Field E] [Field K] [Algebra E K]
  {w : NumberField.InfinitePlace K}
  {σ : NumberField.InfPlaceDecomp.decomp E K w}
-- given
  (h : (σ : K ≃ₐ[E] K) • w = w) :
-- imply
  AlgEquiv.InfinitePlaceTransport.transport (σ : K ≃ₐ[E] K) h = NumberField.InfPlaceDecomp.actRingEquiv σ :=
-- proof
  rfl


-- created on 2026-10-23
