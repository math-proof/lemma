import Lemma.ModularCurve.CycSubRootBridge
import Lemma.WeierstrassCurve.FullKernelQuotient
import Abbrev.ModularCurve_CycSubRootBridgeN

set_option autoImplicit false

noncomputable section

open ModularCurve WeierstrassCurve Polynomial
open scoped Classical

namespace ModularCurve.TatePoint

theorem isElliptic_fullKernelQuotient_cycSubGen (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N]
    (hW3 : FullKernelDiscAt N) (G : CycSubH E N) :
    (E.fullKernelQuotient (cycSubGen E G) N).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (hW3 two_ne_zero E (cycSubGen E G) (addOrderOf_cycSubGen E G))⟩

def cycSubRootN (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N] (hW1 : FullKernelIsRootAt N)
    (hW3 : FullKernelDiscAt N) (data : ModularPolynomialData N) (G : CycSubH E N) : RootsAt data E.j :=
  ⟨@WeierstrassCurve.j H _ (E.fullKernelQuotient (cycSubGen E G) N)
      (isElliptic_fullKernelQuotient_cycSubGen E hW3 G),
    hW1 E (cycSubGen E G) (addOrderOf_cycSubGen E G)
      (isElliptic_fullKernelQuotient_cycSubGen E hW3 G).isUnit.ne_zero data⟩

theorem cycSubRootN_coe (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N]
    (hW1 : FullKernelIsRootAt N) (hW3 : FullKernelDiscAt N) (data : ModularPolynomialData N)
    (G : CycSubH E N) :
    (cycSubRootN E hW1 hW3 data G).1 =
      @WeierstrassCurve.j H _ (E.fullKernelQuotient (cycSubGen E G) N)
        (isElliptic_fullKernelQuotient_cycSubGen E hW3 G) := rfl

theorem cycSubRootN_injective (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N]
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N)
    (data : ModularPolynomialData N) (hj : Transcendental Qbar E.j) :
    Function.Injective (cycSubRootN E hW1 hW3 data) := by
  intro G G' h
  have hjj := congrArg Subtype.val h
  simp only [cycSubRootN_coe] at hjj
  apply CycSubH.ext
  rw [coe_eq_zmultiples_cycSubGen, coe_eq_zmultiples_cycSubGen]
  exact hW2 E (transcendental_rat_of_transcendental_qbar hj) (cycSubGen E G) (cycSubGen E G')
    (addOrderOf_cycSubGen E G) (addOrderOf_cycSubGen E G')
    (isElliptic_fullKernelQuotient_cycSubGen E hW3 G).isUnit.ne_zero
    (isElliptic_fullKernelQuotient_cycSubGen E hW3 G').isUnit.ne_zero hjj

theorem cycSubRootN_bijective (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N]
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N)
    (data : ModularPolynomialData N) (hj : Transcendental Qbar E.j) :
    Function.Bijective (cycSubRootN E hW1 hW3 data) := by
  haveI := finite_rootsAt data E.j
  refine (cycSubRootN_injective E hW1 hW2 hW3 data hj).bijective_of_nat_card_le ?_
  rw [natCard_cycSubH]
  exact natCard_rootsAt_le data E.j

def rootsEquivCycSubHN (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N]
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N)
    (data : ModularPolynomialData N) (hj : Transcendental Qbar E.j) : RootsAt data E.j ≃ CycSubH E N :=
  (Equiv.ofBijective (cycSubRootN E hW1 hW3 data) (cycSubRootN_bijective E hW1 hW2 hW3 data hj)).symm

theorem rootsEquivCycSubHN_symm_apply (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N]
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N)
    (data : ModularPolynomialData N) (hj : Transcendental Qbar E.j) (G : CycSubH E N) :
    (rootsEquivCycSubHN E hW1 hW2 hW3 data hj).symm G = cycSubRootN E hW1 hW3 data G := rfl

theorem rootsEquivCycSubHN_apply_eq_iff (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N]
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N)
    (data : ModularPolynomialData N) (hj : Transcendental Qbar E.j) (r : RootsAt data E.j)
    (G : CycSubH E N) :
    rootsEquivCycSubHN E hW1 hW2 hW3 data hj r = G ↔ r = cycSubRootN E hW1 hW3 data G := by
  rw [← rootsEquivCycSubHN_symm_apply E hW1 hW2 hW3 data hj G, Equiv.eq_symm_apply]

def dictN (N : ℕ) [NeZero N] (data : ModularPolynomialData N) (j₀ : Qbar) (hW1 : FullKernelIsRootAt N)
    (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N) :
    RootsAt data (nearCurve j₀).j ≃ CycSubH (nearCurve j₀) N :=
  rootsEquivCycSubHN (nearCurve j₀) hW1 hW2 hW3 data (nearCurve_j_transcendental j₀)

theorem dictN_symm_apply_coe (N : ℕ) [NeZero N] (data : ModularPolynomialData N) (j₀ : Qbar)
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N)
    (G : CycSubH (nearCurve j₀) N) :
    ((dictN N data j₀ hW1 hW2 hW3).symm G).1 =
      @WeierstrassCurve.j H _ ((nearCurve j₀).fullKernelQuotient (cycSubGen (nearCurve j₀) G) N)
        (isElliptic_fullKernelQuotient_cycSubGen (nearCurve j₀) hW3 G) := rfl

theorem dictN_apply_eq_iff (N : ℕ) [NeZero N] (data : ModularPolynomialData N) (j₀ : Qbar)
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N)
    (r : RootsAt data (nearCurve j₀).j) (G : CycSubH (nearCurve j₀) N) :
    dictN N data j₀ hW1 hW2 hW3 r = G ↔ r = cycSubRootN (nearCurve j₀) hW1 hW3 data G :=
  rootsEquivCycSubHN_apply_eq_iff (nearCurve j₀) hW1 hW2 hW3 data (nearCurve_j_transcendental j₀) r G

end ModularCurve.TatePoint

end

example (N : ℕ) [NeZero N] (h : ∀ [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    (Q : W.toAffine.Point) (_ : addOrderOf Q = N)
    (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData N),
    haveI : (W.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (data.Φ.map (Polynomial.eval₂RingHom
      (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) W.j)).IsRoot
      (W.fullKernelQuotient Q N).j) : ModularCurve.TatePoint.FullKernelIsRootAt N := h
example (N : ℕ) [NeZero N] (h : ModularCurve.TatePoint.FullKernelIsRootAt N)
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData N) :
    haveI : (W.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (data.Φ.map (Polynomial.eval₂RingHom
      (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) W.j)).IsRoot
      (W.fullKernelQuotient Q N).j := h W Q hQ hΔ data
example (N : ℕ) [NeZero N] (h : ∀ [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    (_ : Transcendental ℚ W.j) (Q Q' : W.toAffine.Point)
    (_ : addOrderOf Q = N) (_ : addOrderOf Q' = N)
    (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0)
    (hΔ' : (W.fullKernelQuotient Q' N).Δ ≠ 0)
    (_ : haveI : (W.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
      haveI : (W.fullKernelQuotient Q' N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
      (W.fullKernelQuotient Q N).j = (W.fullKernelQuotient Q' N).j),
    AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') : ModularCurve.TatePoint.FullKernelInjAt N := h
example (N : ℕ) [NeZero N] (h : ModularCurve.TatePoint.FullKernelInjAt N)
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    (ht : Transcendental ℚ W.j) (Q Q' : W.toAffine.Point)
    (hQ : addOrderOf Q = N) (hQ' : addOrderOf Q' = N)
    (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0) (hΔ' : (W.fullKernelQuotient Q' N).Δ ≠ 0)
    (hj : haveI : (W.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
      haveI : (W.fullKernelQuotient Q' N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
      (W.fullKernelQuotient Q N).j = (W.fullKernelQuotient Q' N).j) :
    AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q' := h W ht Q Q' hQ hQ' hΔ hΔ' hj
example (N : ℕ) [NeZero N] (h : ∀ {L : Type} [Field L] [DecidableEq L] [IsAlgClosed L], (2 : L) ≠ 0 →
    ∀ (W : WeierstrassCurve L) [W.IsElliptic] (Q : W.toAffine.Point),
      addOrderOf Q = N → (W.fullKernelQuotient Q N).Δ ≠ 0) : ModularCurve.TatePoint.FullKernelDiscAt N := h
example (N : ℕ) [NeZero N] (h : ModularCurve.TatePoint.FullKernelDiscAt N)
    {L : Type} [Field L] [DecidableEq L] [IsAlgClosed L]
    (h2 : (2 : L) ≠ 0) (W : WeierstrassCurve L) [W.IsElliptic] (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) :
    (W.fullKernelQuotient Q N).Δ ≠ 0 := h h2 W Q hQ
