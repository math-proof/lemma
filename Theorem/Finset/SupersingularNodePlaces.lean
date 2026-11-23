module

public import Theorem.Polynomial.CharLSpecialFibreLevelNDictionary
public import Theorem.WeierstrassCurve.SupersingularModuli
public import Theorem.Scheme.AlgebraicCurveBaseChangeGalois

public noncomputable section

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section Pairs

variable {K F : Type*} [Field K] [Field F] [Algebra K F]


@[simp] public theorem smulNodePair_fst (g : SemilinearAut K F) (w : Place K F) :
    (smulNodePair g w).1 = w := rfl


@[simp] public theorem smulNodePair_snd (g : SemilinearAut K F) (w : Place K F) :
    (smulNodePair g w).2 = g • w := rfl


public theorem smulNodePair_injective (g : SemilinearAut K F) :
    Function.Injective (smulNodePair g) :=
  fun _ _ h => congrArg Prod.fst h


@[simp] public theorem smulNodePairEmb_apply (g : SemilinearAut K F) (w : Place K F) :
    smulNodePairEmb g w = smulNodePair g w := rfl


public theorem mem_nodePairsOfPlaces_iff (g : SemilinearAut K F) (W : Finset (Place K F))
    (s : Place K F × Place K F) :
    s ∈ nodePairsOfPlaces g W ↔ ∃ w ∈ W, smulNodePair g w = s := by
  simp only [nodePairsOfPlaces, Finset.mem_map, smulNodePairEmb_apply]


public theorem smulNodePair_mem_nodePairsOfPlaces (g : SemilinearAut K F)
    {W : Finset (Place K F)} {w : Place K F} (hw : w ∈ W) :
    smulNodePair g w ∈ nodePairsOfPlaces g W :=
  Finset.mem_map_of_mem (smulNodePairEmb g) hw


@[simp] public theorem card_nodePairsOfPlaces (g : SemilinearAut K F) (W : Finset (Place K F)) :
    (nodePairsOfPlaces g W).card = W.card :=
  Finset.card_map _


public theorem fst_mem_of_mem_nodePairsOfPlaces {g : SemilinearAut K F} {W : Finset (Place K F)}
    {s : Place K F × Place K F} (hs : s ∈ nodePairsOfPlaces g W) : s.1 ∈ W := by
  obtain ⟨w, hw, rfl⟩ := (mem_nodePairsOfPlaces_iff g W s).mp hs
  exact hw


public theorem snd_eq_of_mem_nodePairsOfPlaces {g : SemilinearAut K F} {W : Finset (Place K F)}
    {s : Place K F × Place K F} (hs : s ∈ nodePairsOfPlaces g W) : s.2 = g • s.1 := by
  obtain ⟨w, hw, rfl⟩ := (mem_nodePairsOfPlaces_iff g W s).mp hs
  rfl


@[simp] public theorem coe_nodeEquivOfPlaces_apply (g : SemilinearAut K F) (W : Finset (Place K F))
    (w : ↥W) :
    ((nodeEquivOfPlaces g W w : ↥(nodePairsOfPlaces g W)) : Place K F × Place K F)
      = smulNodePair g (w : Place K F) := rfl


@[simp] public theorem coe_nodeEquivOfPlaces_symm_apply (g : SemilinearAut K F)
    (W : Finset (Place K F)) (s : ↥(nodePairsOfPlaces g W)) :
    (((nodeEquivOfPlaces g W).symm s : ↥W) : Place K F)
      = (s : Place K F × Place K F).1 := rfl


public theorem widthOfPlaces_apply (g : SemilinearAut K F) (W : Finset (Place K F))
    (e : Place K F → ℕ) (s : ↥(nodePairsOfPlaces g W)) :
    widthOfPlaces g W e s = e (s : Place K F × Place K F).1 := rfl


@[simp] public theorem widthOfPlaces_mk (g : SemilinearAut K F) {W : Finset (Place K F)}
    (e : Place K F → ℕ) {w : Place K F} (hw : w ∈ W) :
    widthOfPlaces g W e ⟨smulNodePair g w, smulNodePair_mem_nodePairsOfPlaces g hw⟩ = e w :=
  rfl


public theorem widthOfPlaces_nodeEquiv (g : SemilinearAut K F) (W : Finset (Place K F))
    (e : Place K F → ℕ) (w : ↥W) :
    widthOfPlaces g W e (nodeEquivOfPlaces g W w) = e (w : Place K F) := rfl

end Pairs

section Supersingular

variable (q N : ℕ) [NeZero N] (K : Type*) [Field K] [DecidableEq K]


public theorem isSupersingularPlace_iff (w : Place K (modularFunctionFieldC K N)) :
    IsSupersingularPlace q N K w ↔
      w.IsRational ∧ IsAffineGeomPlace K N w ∧ w.evalAt (jGeomGen K N) ∈ ssJSet q K :=
  Iff.rfl


public theorem mem_ssPlaces_iff {w : Place K (modularFunctionFieldC K N)} :
    w ∈ ssPlaces q N K ↔ IsSupersingularPlace q N K w :=
  Iff.rfl

variable {q N K}


public theorem IsSupersingularPlace.isCentreOf_evalAt {w : Place K (modularFunctionFieldC K N)}
    (h : IsSupersingularPlace q N K w) :
    IsCentreOf K N (w.evalAt (jGeomGen K N), w.evalAt (jNGeomGen K N)) w :=
  exists_isCentreOf_of_isRational h.1 h.2.1

end Supersingular

end ModularCurve

end
