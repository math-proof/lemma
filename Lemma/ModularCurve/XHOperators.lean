import Lemma.ModularCurve.XHHeckeOperator
import Lemma.CohCarrier.Inst
import Def.ModularCurve_XHOperators

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace ModularCurve

section Diamond

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)


variable {M H}

theorem isDiamondAutHBar_diamondAutHBar {d : (ZMod M)ˣ}
    (h : ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ) :
    IsDiamondAutHBar M H d (diamondAutHBar M H d) := by
  rw [diamondAutHBar, dif_pos h]
  exact h.choose_spec

theorem diamondAutHBar_of_not {d : (ZMod M)ˣ}
    (h : ¬ ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ) :
    diamondAutHBar M H d = AlgEquiv.refl := by
  rw [diamondAutHBar, dif_neg h]

variable (M H)


theorem diamondHBar_apply (d : (ZMod M)ˣ) (x : JH M H) :
    diamondHBar M H d x = SemilinearAut.ofAlgAut (diamondAutHBar M H d) • x :=
  rfl

theorem diamondHBar_of_not {d : (ZMod M)ˣ}
    (h : ¬ ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ) (x : JH M H) :
    diamondHBar M H d x = x := by
  rw [diamondHBar_apply, diamondAutHBar_of_not h]
  have : SemilinearAut.ofAlgAut
      (AlgEquiv.refl : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H) = 1 :=
    map_one _
  rw [this, one_smul]

end Diamond

section GenOp

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)


theorem genOpH_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) :
    genOpH M H S (.T ℓ hℓ hℓS hℓM) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ) :=
  rfl

theorem genOpH_U (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) :
    genOpH M H S (.U q hq hqM) =
      (haveI : NeZero q := ⟨hq.ne_zero⟩; heckeOperatorHAlong (AlgebraicClosure ℚ) M H q) :=
  rfl

theorem genOpH_dia (d : (ZMod M)ˣ) : genOpH M H S (.dia d) = diamondHBar M H d := rfl

variable (p : ℕ) [Fact p.Prime]


theorem tateGenOpH_apply_coe (g : CohCarrier.Gen M S) (x : TateModule p (JH M H)) (n : ℕ) :
    ((tateGenOpH M H S p g x : TateModule p (JH M H)) : ℕ → JH M H) n =
      genOpH M H S g ((x : ℕ → JH M H) n) :=
  rfl

end GenOp

section Inputs

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)


variable {M H}

theorem HeckeDiamondInputsHAll.heckeInputsHAlong (h : HeckeDiamondInputsHAll M H) (ℓ : ℕ)
    (hℓ : ℓ.Prime) : haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ :=
  h.1 ℓ hℓ

theorem HeckeDiamondInputsHAll.isDiamondAutHBar (h : HeckeDiamondInputsHAll M H) (d : (ZMod M)ˣ) :
    IsDiamondAutHBar M H d (diamondAutHBar M H d) :=
  isDiamondAutHBar_diamondAutHBar (h.2 d)

end Inputs

end ModularCurve

end
