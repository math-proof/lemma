import Mathlib
import Lemma.ModularCurve.GlueData
import Lemma.AlgebraicCurve.GluedPic0
import Def.ModularCurve_NodeDepth
import Lemma.ModularCurve.NodeLocalizedPlaces
import Def.ModularCurve_ProlongationTuple
import Structure.ModularCurve_AnnulusSpecializationLevel
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

namespace ProlongationTuple

variable {P} (R : ProlongationTuple P)


variable {R}
variable {W : Finset (Place k (modularFunctionFieldC k N))} (dat : R.AnnulusDatumLevel W)

namespace AnnulusDatumLevel

open Classical in

def annulusDeg (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) : ℤ :=
  ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V

def chainVal (a : TwistVectorLevel (k := k) (N := N) W) (w : Place k (modularFunctionFieldC k N)) (d : ℕ) : ℤ :=
  if d = 0 then a.aZ else if dat.width w ≤ d then a.aZ' else a.aE w d

def endSlopeFst (a : TwistVectorLevel (k := k) (N := N) W) (w : Place k (modularFunctionFieldC k N)) : ℤ :=
  dat.chainVal a w 1 - dat.chainVal a w 0

def endSlopeSnd (a : TwistVectorLevel (k := k) (N := N) W) (w : Place k (modularFunctionFieldC k N)) : ℤ :=
  dat.chainVal a w (dat.width w - 1) - dat.chainVal a w (dat.width w)

def IsNodeAnnulusPlace (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : Prop :=
  P.reduceFst V ∈ W ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧
    0 < dat.depthQ V ∧ dat.depthQ V < dat.width (P.reduceFst V)

open Classical in

def circleDeg (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) (d : ℕ) : ℚ :=
  ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
    (D V : ℚ) * max 0 (1 - |dat.depthQ V - d|)

def endShareFst (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) : ℤ :=
  if (dat.circleDeg D w 0).den = 1 then (dat.circleDeg D w 0).num else 0

def endShareSnd (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) : ℤ :=
  if (dat.circleDeg D w (dat.width w)).den = 1 then (dat.circleDeg D w (dat.width w)).num else 0

def endOrderFst (a : TwistVectorLevel (k := k) (N := N) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) : ℤ :=
  dat.endSlopeFst a w + dat.endShareFst D w

def endOrderSnd (a : TwistVectorLevel (k := k) (N := N) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) : ℤ :=
  dat.endSlopeSnd a w + dat.endShareSnd D w

def IsTwistOf (a : TwistVectorLevel (k := k) (N := N) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : Prop :=
  Divisor.degree (P.fstDiv D) = -∑ w ∈ W, dat.endOrderFst a D w ∧
    Divisor.degree (P.sndDiv D) = -∑ w ∈ W, dat.endOrderSnd a D w ∧
    ∀ w ∈ W, ∀ d : ℕ, 1 ≤ d → d + 1 ≤ dat.width w →
      dat.circleDeg D w d = -((dat.chainVal a w (d - 1) - 2 * dat.chainVal a w d + dat.chainVal a w (d + 1) : ℤ) : ℚ)

open Classical in

def angCoord (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : k :=
  if h : (dat.depthQ V).den = 1 ∧
      V.evalAt ((dat.coord w hw).y : ↥(modularFunctionFieldBar (N * q))) *
        ((q : AlgebraicClosure ℚ) ^ (dat.depthQ V).num)⁻¹ ∈ A
  then red ⟨_, h.2⟩ else 0

open Classical in
def angUnit (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : kˣ :=
  if h : dat.angCoord w hw V ≠ 0 then Units.mk0 _ h else 1

open Classical in

def depthMoment (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) : ℚ :=
  ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), (D V : ℚ) * dat.depthQ V

open Classical in

def angFactor (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : kˣ :=
  if h : (dat.depthMoment D w).den = 1 ∧
      ∃ hmem : (∏ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
          V.evalAt ((dat.coord w hw).y : ↥(modularFunctionFieldBar (N * q))) ^ (-(D V))) *
        (q : AlgebraicClosure ℚ) ^ (dat.depthMoment D w).num ∈ A, red ⟨_, hmem⟩ ≠ 0
  then Units.mk0 (red ⟨_, h.2.choose⟩) h.2.choose_spec else 1

open Classical in

def crossFst (w' w : Place k (modularFunctionFieldC k N)) : kˣ :=
  if h : w.evalAt (dat.unifFst w') ≠ 0 then Units.mk0 _ h else 1

open Classical in

def crossSnd (w' w : Place k (modularFunctionFieldC k N)) : kˣ :=
  if h : (arithFrobC q k N • w).evalAt (dat.unifSnd w') ≠ 0 then Units.mk0 _ h else 1

open Classical in

def nodeUnitOf (a : TwistVectorLevel (k := k) (N := N) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    ↥(nodePairsOfPlaces (arithFrobC q k N) W) → Additive kˣ := fun s =>
  let w : Place k (modularFunctionFieldC k N) :=
    (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1
  Additive.ofMul <|
    if hw : w ∈ W then
      (-1 : kˣ) ^ (annulusDeg (P := P) D w) *
      dat.u0 w ^ (dat.endOrderSnd a D w) *
      dat.lam w ^ (dat.endOrderFst a D w) *
      (dat.mu w ^ (dat.endOrderSnd a D w))⁻¹ *
      dat.angFactor w hw D *
      (∏ w' ∈ W.erase w,
        (dat.crossFst w' w ^ (dat.endOrderFst a D w'))⁻¹ * dat.crossSnd w' w ^ (dat.endOrderSnd a D w'))
    else 1

def spData (a : TwistVectorLevel (k := k) (N := N) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    GluingData k (modularFunctionFieldC k N) (nodePairsOfPlaces (arithFrobC q k N) W) :=
  (Finsupp.mapDomain P.reduceFst (P.fstDiv D) - ∑ w ∈ W, dat.endOrderFst a D w • dat.corrFst w,
    Finsupp.mapDomain P.reduceSnd (P.sndDiv D) - ∑ w ∈ W, dat.endOrderSnd a D w • dat.corrSnd w,
    dat.nodeUnitOf a D)

open Classical in
def sp (a : TwistVectorLevel (k := k) (N := N) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    GluedPic0 k (modularFunctionFieldC k N) (nodePairsOfPlaces (arithFrobC q k N) W) :=
  if h : dat.spData a D ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) then
    GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W) ⟨dat.spData a D, h⟩
  else 0

end AnnulusDatumLevel

end ProlongationTuple

end ModularCurve.PlaceSpecialization

end
