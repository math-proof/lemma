import Lemma.ModularCurve.NodeLocalizedPlaces

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve

section CrossingCoord

variable {ι : Type*} [Fintype ι]

def crossingCoord (s : ι) : Module.Dual ℤ (characterLattice ι) :=
  (LinearMap.proj s).comp (characterLattice ι).subtype

end CrossingCoord

namespace PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

def depthDiv (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Divisor k (modularFunctionFieldC k N) :=
  D.sum fun V n => Finsupp.single (P.reduceFst V) (n * (depth V : ℤ))

def depthDual (g : SemilinearAut k (modularFunctionFieldC k N))
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Module.Dual ℤ (characterLattice ↥(nodePairsOfPlaces g W)) :=
  ∑ s : ↥(nodePairsOfPlaces g W),
    P.depthDiv depth D
        (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 •
      crossingCoord s

def DepthCompLaw (g : SemilinearAut k (modularFunctionFieldC k N))
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (e : Place k (modularFunctionFieldC k N) → ℕ)
    (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (comp : ↥(inertiaInvariants A (N * q)) →+ componentGroup (widthOfPlaces g W e)) : Prop :=
  ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hH : Pic0.mk D ∈ inertiaInvariants A (N * q)),
    (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ,
          arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
        (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)) →
    ∀ (s₀ : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N))
      (hs₀ : s₀ ∈ nodePairsOfPlaces g W),
      comp ⟨Pic0.mk D, hH⟩ =
        componentGroupProj (widthOfPlaces g W e)
          (P.depthDual g W depth (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) +
            Divisor.degree (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) •
              ((e s₀.1 : ℤ) • crossingCoord ⟨s₀, hs₀⟩))

namespace ProlongationTuple

variable {P} (R : ProlongationTuple P)

def ValueIntegralityLaw (w : Place k (modularFunctionFieldC k N)) : Prop :=
  ∀ f : ↥(modularFunctionFieldBar (N * q)), f ∈ R.nodeIntegers w →
    ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → V.evalAt f ∈ A

namespace NodeCoordinates

variable {R} [PerfectField k] {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
  {w : Place k (modularFunctionFieldC k N)} (c : R.NodeCoordinates K w)

def xDepth (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : A.ValueGroup :=
  A.valuation (V.evalAt (c.x : ↥(modularFunctionFieldBar (N * q))))

def yDepth (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : A.ValueGroup :=
  A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))))

def DepthValueLaw (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ) : Prop :=
  ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
    (∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) →
    c.yDepth V = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ depth V

end NodeCoordinates

end ProlongationTuple

end PlaceSpecialization

end ModularCurve

end
