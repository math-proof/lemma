import Instance.ModularCurve_TateFormal
import Instance.ModularCurve_PhiGen
import Structure.WeierstrassCurve_VeluQuotientMap
import Instance.ModularCurve_TatePoint

set_option autoImplicit false

noncomputable section

open ModularCurve WeierstrassCurve Polynomial

namespace ModularCurve.TatePoint


open scoped Classical in


open scoped Classical in


open scoped Classical in


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


end TatePoint

open scoped Classical in


end ModularCurve.TatePoint

end
