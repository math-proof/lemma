import Lemma.Definitions.Def_ModularCurve_HeckeSeam
import Lemma.Definitions.Def_ModularCurve_ToricDescentData

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

section Functorial

variable (p : ℕ) [Fact p.Prime] {J J' : Type} [AddCommGroup J] [AddCommGroup J']

def tateMap (f : J →+ J') : TateModule p J →+ TateModule p J' where
  toFun x := ⟨fun n => f ((x : ℕ → J) n), fun n =>
    ⟨by rw [← map_zsmul f, TateModule.torsion x n, map_zero],
     by rw [← map_zsmul f, TateModule.compat x n]⟩⟩
  map_zero' := Subtype.ext (funext fun n => by
    show f (((0 : TateModule p J) : ℕ → J) n) = ((0 : TateModule p J') : ℕ → J') n
    rw [TateModule.coe_zero, Pi.zero_apply, map_zero, TateModule.coe_zero, Pi.zero_apply])
  map_add' x y := Subtype.ext (funext fun n => by
    show f (((x + y : TateModule p J) : ℕ → J) n) = _
    rw [TateModule.coe_add, Pi.add_apply, map_add]
    rfl)

omit [Fact (Nat.Prime p)] in
@[simp] theorem tateMap_apply (f : J →+ J') (x : TateModule p J) (n : ℕ) :
    ((tateMap p f x : TateModule p J') : ℕ → J') n = f ((x : ℕ → J) n) :=
  rfl

def tateMapLin (f : J →+ J') : TateModule p J →ₗ[ℤ_[p]] TateModule p J' where
  toFun := tateMap p f
  map_add' := (tateMap p f).map_add
  map_smul' a x := Subtype.ext (funext fun n => by
    rw [RingHom.id_apply]
    show ((tateMap p f (a • x) : TateModule p J') : ℕ → J') n =
      ((a • tateMap p f x : TateModule p J') : ℕ → J') n
    rw [tateMap_apply, TateModule.smul_apply, TateModule.smul_apply, map_zsmul, tateMap_apply])

def vpMap (f : J →+ J') :
    RationalTateModule p J →ₗ[ℚ_[p]] RationalTateModule p J' :=
  LinearMap.baseChange ℚ_[p] (tateMapLin p f)

end Functorial

section OldNew

variable (N q : ℕ) [NeZero N] [NeZero q] (p : ℕ) [Fact p.Prime]

def vpDegeneracyPush (i : Fin 2) :
    RationalTateModule p (JZero (N * q)) →ₗ[ℚ_[p]] RationalTateModule p (JZero N) :=
  vpMap p (degeneracyPushforwardPair N q i)

def newPartVp : Submodule ℚ_[p] (RationalTateModule p (JZero (N * q))) :=
  LinearMap.ker (vpDegeneracyPush N q p 0) ⊓ LinearMap.ker (vpDegeneracyPush N q p 1)

end OldNew

section OldNewPull

variable (N q : ℕ) [NeZero N] [NeZero q] (p : ℕ) [Fact p.Prime]

def DegeneracyPullbackInputs : Prop :=
  ∃ (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (_ : HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))),
    FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα ∧
      FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ

open Classical in

def degeneracyPullbackPair : Fin 2 → (JZero N →+ JZero (N * q)) :=
  if h : DegeneracyPullbackInputs N q then
    ![letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
      haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) N q)
      haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) N q) h.fst
      haveI := h.snd.snd.fst
      haveI : FundamentalIdentity (AlgebraicClosure ℚ)
          ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))) :=
        h.snd.snd.snd.1
      Pic0.pullbackHom _,
      letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) N q)
      haveI := isScalarTower_along (heckeBetaBar (AlgebraicClosure ℚ) N q)
      haveI := isIntegral_along (heckeBetaBar (AlgebraicClosure ℚ) N q) h.snd.fst
      haveI := h.snd.snd.fst
      haveI : FundamentalIdentity (AlgebraicClosure ℚ)
          ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))) :=
        h.snd.snd.snd.2
      Pic0.pullbackHom _]
  else 0

def HeckeTransposeInputsAlong : Prop :=
  ∃ (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (_ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (_ : HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))))
    (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q)),
    FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα ∧
      NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hfin

open Classical in

def heckeOperatorTransposeAlong : JZero N →+ JZero N :=
  if h : HeckeTransposeInputsAlong N q then
    haveI := h.snd.snd.fst
    heckePic0BarTranspose h.fst h.snd.fst h.snd.snd.snd.snd.1 h.snd.snd.snd.fst
      h.snd.snd.snd.snd.2
  else 0

def vpDegeneracyPull (i : Fin 2) :
    RationalTateModule p (JZero N) →ₗ[ℚ_[p]] RationalTateModule p (JZero (N * q)) :=
  vpMap p (degeneracyPullbackPair N q i)

def vpJointPush :
    RationalTateModule p (JZero (N * q)) →ₗ[ℚ_[p]]
      RationalTateModule p (JZero N) × RationalTateModule p (JZero N) :=
  LinearMap.prod (vpDegeneracyPush N q p 0) (vpDegeneracyPush N q p 1)

def vpJointPull :
    RationalTateModule p (JZero N) × RationalTateModule p (JZero N) →ₗ[ℚ_[p]]
      RationalTateModule p (JZero (N * q)) :=
  LinearMap.coprod (vpDegeneracyPull N q p 0) (vpDegeneracyPull N q p 1)

def oldPartVp : Submodule ℚ_[p] (RationalTateModule p (JZero (N * q))) :=
  LinearMap.range (vpJointPull N q p)

def oldNewGramVp :
    Module.End ℚ_[p]
      (RationalTateModule p (JZero N) × RationalTateModule p (JZero N)) :=
  (vpJointPush N q p).comp (vpJointPull N q p)

theorem ker_vpJointPush : LinearMap.ker (vpJointPush N q p) = newPartVp N q p :=
  LinearMap.ker_prod _ _

theorem oldPartVp_eq_sup :
    oldPartVp N q p =
      LinearMap.range (vpDegeneracyPull N q p 0) ⊔ LinearMap.range (vpDegeneracyPull N q p 1) :=
  LinearMap.range_coprod _ _

end OldNewPull

end ModularCurve

end
