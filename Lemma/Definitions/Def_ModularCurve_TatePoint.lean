import Lemma.Definitions.Def_ModularCurve_TateFormal
import Lemma.Definitions.Def_ModularCurve_PhiGen
import Lemma.Definitions.Def_WeierstrassCurve_VeluQuotientMap

set_option autoImplicit false

noncomputable section

open ModularCurve WeierstrassCurve Polynomial

namespace ModularCurve.TatePoint

abbrev Qbar : Type := AlgebraicClosure ℚ

abbrev H : Type := HahnSeries ℚ Qbar

def jNear (j₀ : Qbar) : H := HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : Qbar)

open scoped Classical in

def nearCurve (j₀ : Qbar) : WeierstrassCurve H := WeierstrassCurve.ofJ (jNear j₀)

open scoped Classical in
instance instIsElliptic_nearCurve (j₀ : Qbar) : (nearCurve j₀).IsElliptic := by
  unfold nearCurve; infer_instance

open scoped Classical in

def CycSubH (E : WeierstrassCurve H) (N : ℕ) : Type :=
  {G : AddSubgroup E.toAffine.Point //
    ∃ g : E.toAffine.Point, addOrderOf g = N ∧ G = AddSubgroup.zmultiples g}

def RootsAt {p : ℕ} [NeZero p] (data : ModularPolynomialData p) (jv : H) : Type :=
  {y : H // (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom H) jv)).IsRoot y}

open scoped Classical in

theorem nearCurve_j (j₀ : Qbar) : (nearCurve j₀).j = jNear j₀ :=
  WeierstrassCurve.ofJ_j (jNear j₀)

theorem nearCurve_j_transcendental (j₀ : Qbar) : Transcendental Qbar (nearCurve j₀).j := by
  rw [nearCurve_j]
  intro halg
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible Qbar (minpoly.irreducible halg.isIntegral)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one Qbar _ hdeg
  have hC : algebraMap Qbar H c = HahnSeries.C c := by
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]
  rw [hC] at hc
  have h1 := congrArg (fun x : H => x.coeff (1 : ℚ)) hc
  simp only [jNear, HahnSeries.C_apply, HahnSeries.coeff_add, HahnSeries.coeff_single_same,
    HahnSeries.coeff_single_of_ne (one_ne_zero : (1 : ℚ) ≠ 0), zero_add] at h1
  exact zero_ne_one h1

section TatePoint

variable (K : Type) [Field K] [Algebra ℚ K]
variable (p : ℕ) [Fact (Nat.Prime p)] [NeZero p] (ζ : Kˣ)

def basePoint : WeierstrassCurve (LaurentSeries K) := (tateLaurent K).map (qExpand K p)

variable (veluSlotSet : Fin (p + 1) → Finset (LaurentSeries K × LaurentSeries K))

def slotQuotient (i : Fin (p + 1)) : WeierstrassCurve (LaurentSeries K) :=
  (basePoint K p).veluQuotient (veluSlotSet i)

variable (instQ : ∀ i, (slotQuotient K p veluSlotSet i).IsElliptic)

structure W4Conclusions (data : ModularPolynomialData p) : Prop where

  oddVeluSet : ∀ i, (basePoint K p).IsOddVeluSet (veluSlotSet i)

  slotCurve_succ : ∀ b : Fin p,
    ((tateLaurent K).map (qTwist (ζ ^ (b : ℕ)))).j = PhiGen.conj p ζ b.succ

  slotCurve_zero : ((tateLaurent K).map (qExpand K (p * p))).j = PhiGen.conj p ζ 0

  nonToric : ∀ b : Fin p,
    slotQuotient K p veluSlotSet b.succ = (tateLaurent K).map (qTwist (ζ ^ (b : ℕ)))

  dictionary : data.Φ.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) =
    ∏ i : Fin (p + 1),
      (X - C (@WeierstrassCurve.j _ _ (slotQuotient K p veluSlotSet i) (instQ i)))

  distinct : Function.Injective fun i : Fin (p + 1) =>
    @WeierstrassCurve.j _ _ (slotQuotient K p veluSlotSet i) (instQ i)

open scoped Classical in

def W3Proper : Prop :=
  ∀ i, (veluSlotSet i).card = (p - 1) / 2 ∧
    ∃ g : (basePoint K p).toAffine.Point, addOrderOf g = p ∧
      ∀ P ∈ veluSlotSet i, ∃ (k : ℕ) (h : (basePoint K p).toAffine.Nonsingular P.1 P.2),
        0 < k ∧ (k • g : (basePoint K p).toAffine.Point) = WeierstrassCurve.Affine.Point.some P.1 P.2 h

end TatePoint

open scoped Classical in

def ModuliDictionary (p : ℕ) [NeZero p] (data : ModularPolynomialData p) : Prop :=
  ∀ (E : WeierstrassCurve H) [E.IsElliptic], Transcendental Qbar E.j →
    Nonempty {e : RootsAt data E.j ≃ CycSubH E p //
      ∀ r : RootsAt data E.j, ∃ S : Finset (H × H),
        E.IsOddVeluSet S ∧
        (∀ P ∈ S, ∃ h : E.toAffine.Nonsingular P.1 P.2,
          WeierstrassCurve.Affine.Point.some P.1 P.2 h ∈ (e r).1) ∧
        ∃ hQ : (E.veluQuotient S).IsElliptic,
          @WeierstrassCurve.j H _ (E.veluQuotient S) hQ = r.1}

end ModularCurve.TatePoint

end
