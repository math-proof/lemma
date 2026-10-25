import Lemma.ModularCurve.CycSubRootBridge
import Def.WeierstrassCurve_FullKernelQuotient

set_option autoImplicit false

noncomputable section

open ModularCurve WeierstrassCurve Polynomial
open scoped Classical

namespace ModularCurve.TatePoint

abbrev FullKernelIsRootAt (N : ℕ) [NeZero N] : Prop :=
  ∀ [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    (Q : W.toAffine.Point) (_ : addOrderOf Q = N)
    (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData N),
    haveI : (W.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (data.Φ.map (Polynomial.eval₂RingHom
      (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) W.j)).IsRoot
      (W.fullKernelQuotient Q N).j

abbrev FullKernelInjAt (N : ℕ) [NeZero N] : Prop :=
  ∀ [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    (_ : Transcendental ℚ W.j) (Q Q' : W.toAffine.Point)
    (_ : addOrderOf Q = N) (_ : addOrderOf Q' = N)
    (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0)
    (hΔ' : (W.fullKernelQuotient Q' N).Δ ≠ 0)
    (_ : haveI : (W.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
      haveI : (W.fullKernelQuotient Q' N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
      (W.fullKernelQuotient Q N).j = (W.fullKernelQuotient Q' N).j),
    AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q'

abbrev FullKernelDiscAt (N : ℕ) [NeZero N] : Prop :=
  ∀ {L : Type} [Field L] [DecidableEq L] [IsAlgClosed L], (2 : L) ≠ 0 →
    ∀ (W : WeierstrassCurve L) [W.IsElliptic] (Q : W.toAffine.Point),
      addOrderOf Q = N → (W.fullKernelQuotient Q N).Δ ≠ 0

attribute [local instance] isAlgClosed_H charZero_H

end ModularCurve.TatePoint

end
