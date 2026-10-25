import Def.ModularCurve_LevelOneGlueData
import Lemma.AlgebraicCurve.GluedPic0
import Def.ModularCurve_NodeDepth
import Lemma.ModularCurve.NodeLocalizedPlaces
import Def.ModularCurve_ProlongationTuple
import Structure.ModularCurve_LevelOneAnnulusSpecialization
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

namespace ProlongationTuple

variable {P} (R : ProlongationTuple P)


variable {R}
variable {W : Finset (Place k (modularFunctionFieldC k 1))} (dat : R.AnnulusDatum W)

namespace AnnulusDatum

def chainVal (a : TwistVector (k := k) W) (w : Place k (modularFunctionFieldC k 1)) (d : ℕ) : ℤ :=
  if d = 0 then a.aZ else if dat.width w ≤ d then a.aZ' else a.aE w d

def endSlopeFst (a : TwistVector (k := k) W) (w : Place k (modularFunctionFieldC k 1)) : ℤ :=
  dat.chainVal a w 1 - dat.chainVal a w 0

def endSlopeSnd (a : TwistVector (k := k) W) (w : Place k (modularFunctionFieldC k 1)) : ℤ :=
  dat.chainVal a w (dat.width w - 1) - dat.chainVal a w (dat.width w)

def IsNodeAnnulusPlace (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  P.reduceFst V ∈ W ∧
    (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V) ∧
    0 < dat.depth V ∧ dat.depth V < dat.width (P.reduceFst V)

open Classical in
def annulusDeg (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (w : Place k (modularFunctionFieldC k 1)) : ℤ :=
  ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V

open Classical in
def circleDeg (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (w : Place k (modularFunctionFieldC k 1)) (d : ℕ) : ℤ :=
  ∑ V ∈ D.support with (P.reduceFst V = w ∧ dat.depth V = d ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V

def IsTwistOf (a : TwistVector (k := k) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  Divisor.degree (P.fstDiv D) = -∑ w ∈ W, dat.endSlopeFst a w ∧
    Divisor.degree (P.sndDiv D) = -∑ w ∈ W, dat.endSlopeSnd a w ∧
    ∀ w ∈ W, ∀ d : ℕ, 1 ≤ d → d + 1 ≤ dat.width w →
      dat.circleDeg D w d = -(dat.chainVal a w (d - 1) - 2 * dat.chainVal a w d + dat.chainVal a w (d + 1))

open Classical in

def angCoord (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : k :=
  if h : V.evalAt ((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q))) *
      ((q : AlgebraicClosure ℚ) ^ dat.depth V)⁻¹ ∈ A
  then red ⟨_, h⟩ else 0

open Classical in
def angUnit (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : kˣ :=
  if h : dat.angCoord w hw V ≠ 0 then Units.mk0 _ h else 1

open Classical in

def crossFst (w' w : Place k (modularFunctionFieldC k 1)) : kˣ :=
  if h : w.evalAt (dat.unifFst w') ≠ 0 then Units.mk0 _ h else 1

open Classical in

def crossSnd (w' w : Place k (modularFunctionFieldC k 1)) : kˣ :=
  if h : (arithFrobC q k 1 • w).evalAt (dat.unifSnd w') ≠ 0 then Units.mk0 _ h else 1

open Classical in

def nodeUnitOf (a : TwistVector (k := k) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    ↥(nodePairsOfPlaces (arithFrobC q k 1) W) → Additive kˣ := fun s =>
  let w : Place k (modularFunctionFieldC k 1) :=
    (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1
  Additive.ofMul <|
    if hw : w ∈ W then
      (-1 : kˣ) ^ (annulusDeg (P := P) D w) *
      dat.u0 w ^ (dat.endSlopeSnd a w) *
      dat.lam w ^ (dat.endSlopeFst a w) *
      (dat.mu w ^ (dat.endSlopeSnd a w))⁻¹ *
      (∏ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
        dat.angUnit w hw V ^ (-(D V))) *
      (∏ w' ∈ W.erase w,
        (dat.crossFst w' w ^ (dat.endSlopeFst a w'))⁻¹ * dat.crossSnd w' w ^ (dat.endSlopeSnd a w'))
    else 1

def spData (a : TwistVector (k := k) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    GluingData k (modularFunctionFieldC k 1) (nodePairsOfPlaces (arithFrobC q k 1) W) :=
  (Finsupp.mapDomain P.reduceFst (P.fstDiv D)
      - Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv D)) • Finsupp.single dat.cusp 1,
    Finsupp.mapDomain P.reduceSnd (P.sndDiv D)
      - Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)) • Finsupp.single dat.cusp 1,
    dat.nodeUnitOf a D)

open Classical in
def sp (a : TwistVector (k := k) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    GluedPic0 k (modularFunctionFieldC k 1) (nodePairsOfPlaces (arithFrobC q k 1) W) :=
  if h : dat.spData a D ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W) then
    GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W) ⟨dat.spData a D, h⟩
  else 0

end AnnulusDatum

end ProlongationTuple

end ModularCurve.PlaceSpecialization

end
