import Lemma.Definitions.Def_ModularCurve_CycSubRootBridge

set_option autoImplicit false

noncomputable section

open ModularCurve WeierstrassCurve Polynomial
open scoped Classical

namespace ModularCurve.TatePoint

attribute [local instance] isAlgClosed_H charZero_H

theorem two_mul_pred_div_two_add_one_of_odd {N : ℕ} (hN : Odd N) : 2 * ((N - 1) / 2) + 1 = N := by
  obtain ⟨m, rfl⟩ := hN
  omega

theorem isElliptic_veluQuotient_cycSubSummingSet_of_odd (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ}
    (hN : Odd N) (G : CycSubH E N) :
    (E.veluQuotient (cycSubSummingSet E G)).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr
    (WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero (L := H) two_ne_zero E
      ((N - 1) / 2) (cycSubGen E G)
      (by rw [addOrderOf_cycSubGen, two_mul_pred_div_two_add_one_of_odd hN]))⟩

def cycSubRootOdd (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N] (hN : Odd N)
    (data : ModularPolynomialData N) (G : CycSubH E N) : RootsAt data E.j :=
  ⟨@WeierstrassCurve.j H _ (E.veluQuotient (cycSubSummingSet E G))
      (isElliptic_veluQuotient_cycSubSummingSet_of_odd E hN G),
    isRoot_map_j_veluQuotient_j_of_eq E ((N - 1) / 2) (two_mul_pred_div_two_add_one_of_odd hN) data
      (cycSubGen E G) (addOrderOf_cycSubGen E G)
      (isElliptic_veluQuotient_cycSubSummingSet_of_odd E hN G).isUnit.ne_zero⟩

theorem cycSubRootOdd_coe (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N] (hN : Odd N)
    (data : ModularPolynomialData N) (G : CycSubH E N) :
    (cycSubRootOdd E hN data G).1 =
      @WeierstrassCurve.j H _ (E.veluQuotient (cycSubSummingSet E G))
        (isElliptic_veluQuotient_cycSubSummingSet_of_odd E hN G) := rfl

theorem cycSubRootOdd_injective (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N] (hN : Odd N)
    (data : ModularPolynomialData N) (hj : Transcendental Qbar E.j) :
    Function.Injective (cycSubRootOdd E hN data) := by
  intro G G' h
  have hjj := congrArg Subtype.val h
  simp only [cycSubRootOdd_coe] at hjj
  apply CycSubH.ext
  rw [coe_eq_zmultiples_cycSubGen, coe_eq_zmultiples_cycSubGen]
  exact WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental E
    (transcendental_rat_of_transcendental_qbar hj) ((N - 1) / 2) (cycSubGen E G) (cycSubGen E G')
    (by rw [addOrderOf_cycSubGen, two_mul_pred_div_two_add_one_of_odd hN])
    (by rw [addOrderOf_cycSubGen, two_mul_pred_div_two_add_one_of_odd hN])
    (isElliptic_veluQuotient_cycSubSummingSet_of_odd E hN G).isUnit.ne_zero
    (isElliptic_veluQuotient_cycSubSummingSet_of_odd E hN G').isUnit.ne_zero hjj

theorem cycSubRootOdd_bijective (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N] (hN : Odd N)
    (data : ModularPolynomialData N) (hj : Transcendental Qbar E.j) :
    Function.Bijective (cycSubRootOdd E hN data) := by
  haveI := finite_rootsAt data E.j
  refine (cycSubRootOdd_injective E hN data hj).bijective_of_nat_card_le ?_
  rw [natCard_cycSubH]
  exact natCard_rootsAt_le data E.j

def rootsEquivCycSubHOdd (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N] (hN : Odd N)
    (data : ModularPolynomialData N) (hj : Transcendental Qbar E.j) : RootsAt data E.j ≃ CycSubH E N :=
  (Equiv.ofBijective (cycSubRootOdd E hN data) (cycSubRootOdd_bijective E hN data hj)).symm

theorem rootsEquivCycSubHOdd_symm_apply (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N]
    (hN : Odd N) (data : ModularPolynomialData N) (hj : Transcendental Qbar E.j) (G : CycSubH E N) :
    (rootsEquivCycSubHOdd E hN data hj).symm G = cycSubRootOdd E hN data G := rfl

theorem rootsEquivCycSubHOdd_apply_eq_iff (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N]
    (hN : Odd N) (data : ModularPolynomialData N) (hj : Transcendental Qbar E.j) (r : RootsAt data E.j)
    (G : CycSubH E N) :
    rootsEquivCycSubHOdd E hN data hj r = G ↔ r = cycSubRootOdd E hN data G := by
  rw [← rootsEquivCycSubHOdd_symm_apply E hN data hj G, Equiv.eq_symm_apply]

def dictOdd (N : ℕ) [NeZero N] (hN : Odd N) (data : ModularPolynomialData N) (j₀ : Qbar) :
    RootsAt data (nearCurve j₀).j ≃ CycSubH (nearCurve j₀) N :=
  rootsEquivCycSubHOdd (nearCurve j₀) hN data (nearCurve_j_transcendental j₀)

theorem dictOdd_symm_apply_coe (N : ℕ) [NeZero N] (hN : Odd N) (data : ModularPolynomialData N)
    (j₀ : Qbar) (G : CycSubH (nearCurve j₀) N) :
    ((dictOdd N hN data j₀).symm G).1 =
      @WeierstrassCurve.j H _ ((nearCurve j₀).veluQuotient (cycSubSummingSet (nearCurve j₀) G))
        (isElliptic_veluQuotient_cycSubSummingSet_of_odd (nearCurve j₀) hN G) := rfl

theorem dictOdd_apply_eq_iff (N : ℕ) [NeZero N] (hN : Odd N) (data : ModularPolynomialData N)
    (j₀ : Qbar) (r : RootsAt data (nearCurve j₀).j) (G : CycSubH (nearCurve j₀) N) :
    dictOdd N hN data j₀ r = G ↔ r = cycSubRootOdd (nearCurve j₀) hN data G :=
  rootsEquivCycSubHOdd_apply_eq_iff (nearCurve j₀) hN data (nearCurve_j_transcendental j₀) r G

end ModularCurve.TatePoint

end
