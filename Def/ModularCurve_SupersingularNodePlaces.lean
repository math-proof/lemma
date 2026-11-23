import Theorem.Polynomial.CharLSpecialFibreLevelNDictionary
import Lemma.WeierstrassCurve.SupersingularModuli
import Theorem.Scheme.AlgebraicCurveBaseChangeGalois

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section Pairs

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def smulNodePair (g : SemilinearAut K F) (w : Place K F) : Place K F × Place K F :=
  (w, g • w)

def smulNodePairEmb (g : SemilinearAut K F) : Place K F ↪ Place K F × Place K F :=
  ⟨smulNodePair g, smulNodePair_injective g⟩

def nodePairsOfPlaces (g : SemilinearAut K F) (W : Finset (Place K F)) :
    Finset (Place K F × Place K F) :=
  W.map (smulNodePairEmb g)

def nodeEquivOfPlaces (g : SemilinearAut K F) (W : Finset (Place K F)) :
    ↥W ≃ ↥(nodePairsOfPlaces g W) where
  toFun w := ⟨smulNodePair g w, smulNodePair_mem_nodePairsOfPlaces g w.2⟩
  invFun s := ⟨(s : Place K F × Place K F).1, fst_mem_of_mem_nodePairsOfPlaces s.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv s := Subtype.ext
    (Prod.ext rfl (snd_eq_of_mem_nodePairsOfPlaces s.2).symm)

def widthOfPlaces (g : SemilinearAut K F) (W : Finset (Place K F)) (e : Place K F → ℕ) :
    ↥(nodePairsOfPlaces g W) → ℕ :=
  fun s => e (s : Place K F × Place K F).1

end Pairs

section Supersingular

variable (q N : ℕ) [NeZero N] (K : Type*) [Field K] [DecidableEq K]

def IsSupersingularPlace (w : Place K (modularFunctionFieldC K N)) : Prop :=
  w.IsRational ∧ IsAffineGeomPlace K N w ∧ w.evalAt (jGeomGen K N) ∈ ssJSet q K

def ssPlaces : Set (Place K (modularFunctionFieldC K N)) :=
  {w | IsSupersingularPlace q N K w}

variable {q N K}

end Supersingular

end ModularCurve

end
