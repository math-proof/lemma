import Lemma.Definitions.Def_LanglandsTunnell_ConverseData

noncomputable section

namespace LanglandsTunnell

open Complex NumberField

namespace RealArchParam

def baseChange : RealArchParam → ComplexArchParam
  | principal u₁ _ u₂ _ => ⟨u₁, 0, u₂, 0⟩
  | discrete u k _ => ⟨u, (k : ℤ), u, -(k : ℤ)⟩

theorem baseChange_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    (principal u₁ a₁ u₂ a₂).baseChange = ⟨u₁, 0, u₂, 0⟩ := rfl

theorem baseChange_discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (discrete u k hk).baseChange = ⟨u, (k : ℤ), u, -(k : ℤ)⟩ := rfl

theorem centralTwist_baseChange (P : RealArchParam) : P.baseChange.centralTwist = 0 := by
  cases P <;> simp [baseChange, ComplexArchParam.centralTwist]

theorem centralExponent_baseChange (P : RealArchParam) :
    P.baseChange.centralExponent = P.centralExponent := by
  cases P <;> simp [baseChange, ComplexArchParam.centralExponent, centralExponent, two_mul]

theorem baseChange_oddArtin : oddArtin.baseChange = ComplexArchParam.trivialArtin := rfl

theorem gammaC_baseChange_twist_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) (u : ℂ)
    (k : ℤ) :
    ((principal u₁ a₁ u₂ a₂).baseChange.twist u k).gammaC =
      {u₁ + u + (k.natAbs : ℂ) / 2, u₂ + u + (k.natAbs : ℂ) / 2} := by
  simp [baseChange, ComplexArchParam.twist, ComplexArchParam.gammaC]

theorem gammaC_baseChange_twist_discrete (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀) (u : ℂ) :
    ((discrete u₀ k₀ hk).baseChange.twist u 0).gammaC =
      {u₀ + u + (k₀ : ℂ) / 2, u₀ + u + (k₀ : ℂ) / 2} := by
  simp [baseChange, ComplexArchParam.twist, ComplexArchParam.gammaC]

theorem gammaC_baseChange_dual (P : RealArchParam) :
    P.dual.baseChange.gammaC = P.baseChange.dual.gammaC := by
  cases P <;> simp [baseChange, dual, ComplexArchParam.dual, ComplexArchParam.gammaC]

theorem gammaC_baseChange_dual_twist (P : RealArchParam) (u : ℂ) (k : ℤ) :
    (P.dual.baseChange.twist u k).gammaC = (P.baseChange.dual.twist u k).gammaC := by
  cases P with
  | principal u₁ a₁ u₂ a₂ =>
    simp [baseChange, dual, ComplexArchParam.dual, ComplexArchParam.twist, ComplexArchParam.gammaC]
  | discrete u₀ k₀ hk =>
    simp only [baseChange, dual, ComplexArchParam.dual, ComplexArchParam.twist,
      ComplexArchParam.gammaC, neg_neg]
    exact Multiset.pair_comm _ _

theorem epsilonFactor_baseChange_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    (principal u₁ a₁ u₂ a₂).baseChange.epsilonFactor = 1 := by
  simp [baseChange, ComplexArchParam.epsilonFactor]

theorem epsilonFactor_baseChange_discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (discrete u k hk).baseChange.epsilonFactor = (-1) ^ k := by
  simp only [baseChange, ComplexArchParam.epsilonFactor, Int.natAbs_neg, Int.natAbs_natCast,
    ← pow_add, ← two_mul, pow_mul, I_sq]

theorem Gammaℝ_signShift_mul (x : ℂ) (b : ZMod 2) :
    Gammaℝ (x + signShift b) * Gammaℝ (x + signShift (b + 1)) = Gammaℂ x := by
  have h := Gammaℝ_mul_Gammaℝ_add_one x
  have h' : Gammaℝ (x + 1) * Gammaℝ x = Gammaℂ x := by rw [mul_comm]; exact h
  fin_cases b
  · change Gammaℝ (x + signShift 0) * Gammaℝ (x + signShift (0 + 1)) = Gammaℂ x
    rw [zero_add, signShift_zero, signShift_one, add_zero]
    exact h
  · change Gammaℝ (x + signShift 1) * Gammaℝ (x + signShift (1 + 1)) = Gammaℂ x
    rw [show (1 : ZMod 2) + 1 = 0 by decide, signShift_zero, signShift_one, add_zero]
    exact h'

theorem archFactor_baseChange_twist_discrete (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀) (u : ℂ) (a : ZMod 2)
    (s : ℂ) :
    ((discrete u₀ k₀ hk).baseChange.twist u 0).archFactor s =
      ((discrete u₀ k₀ hk).twist u a).archFactor s *
        ((discrete u₀ k₀ hk).twist u (a + 1)).archFactor s := by
  simp [ComplexArchParam.archFactor, archFactor, gammaC_baseChange_twist_discrete, twist, gammaR,
    gammaC]

theorem archFactor_baseChange_twist_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) (u : ℂ)
    (a : ZMod 2) (s : ℂ) :
    ((principal u₁ a₁ u₂ a₂).baseChange.twist u 0).archFactor s =
      ((principal u₁ a₁ u₂ a₂).twist u a).archFactor s *
        ((principal u₁ a₁ u₂ a₂).twist u (a + 1)).archFactor s := by
  have h₁ := Gammaℝ_signShift_mul (s + (u₁ + u)) (a₁ + a)
  have h₂ := Gammaℝ_signShift_mul (s + (u₂ + u)) (a₂ + a)
  simp only [ComplexArchParam.archFactor, archFactor, gammaC_baseChange_twist_principal, twist,
    gammaR, gammaC, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, Multiset.map_zero, Multiset.prod_zero, mul_one,
    Int.natAbs_zero, Nat.cast_zero, zero_div, add_zero, add_assoc] at h₁ h₂ ⊢
  rw [mul_mul_mul_comm, h₁, h₂]

end RealArchParam

namespace Converse

variable (K : Type) [Field K]

def archOfParamR (P : RealArchParam) : ∀ w : InfinitePlace K, w.IsReal → RealArchParam :=
  fun _ _ => P

def archOfParamC (P : RealArchParam) : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam :=
  fun _ _ => P.baseChange

theorem archOfParamR_apply (P : RealArchParam) (w : InfinitePlace K) (hw : w.IsReal) :
    archOfParamR K P w hw = P := rfl

theorem archOfParamC_apply (P : RealArchParam) (w : InfinitePlace K) (hw : w.IsComplex) :
    archOfParamC K P w hw = P.baseChange := rfl

variable [NumberField K]

abbrev rsGammaR (P : RealArchParam) (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) : Multiset ℂ :=
  twistedGammaR K (archOfParamR K P) uR aR

abbrev rsGammaC (P : RealArchParam) (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) : Multiset ℂ :=
  twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC

theorem rsGammaR_def (P : RealArchParam) (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) :
    rsGammaR K P uR aR = twistedGammaR K (archOfParamR K P) uR aR := rfl

theorem rsGammaC_def (P : RealArchParam) (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) :
    rsGammaC K P uR aR uC kC = twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC :=
  rfl

theorem rsGammaR_const (P : RealArchParam) (u : ℂ) (a : ZMod 2) :
    rsGammaR K P (fun _ _ => u) (fun _ _ => a) =
      InfinitePlace.nrRealPlaces K • (P.twist u a).gammaR := by
  simp [rsGammaR, twistedGammaR, archOfParamR, Finset.sum_const, Finset.card_univ]

theorem rsGammaC_const (P : RealArchParam) (u : ℂ) (a : ZMod 2) (u' : ℂ) (k' : ℤ) :
    rsGammaC K P (fun _ _ => u) (fun _ _ => a) (fun _ _ => u') (fun _ _ => k') =
      InfinitePlace.nrRealPlaces K • (P.twist u a).gammaC +
        InfinitePlace.nrComplexPlaces K • (P.baseChange.twist u' k').gammaC := by
  simp [rsGammaC, twistedGammaC, archOfParamR, archOfParamC, Finset.sum_const, Finset.card_univ]

theorem rsGammaR_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) (u : ℂ) (a : ZMod 2) :
    rsGammaR K (.principal u₁ a₁ u₂ a₂) (fun _ _ => u) (fun _ _ => a) =
      InfinitePlace.nrRealPlaces K •
        ({u₁ + u + signShift (a₁ + a), u₂ + u + signShift (a₂ + a)} : Multiset ℂ) := by
  rw [rsGammaR_const]; rfl

theorem rsGammaR_discrete (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀) (u : ℂ) (a : ZMod 2) :
    rsGammaR K (.discrete u₀ k₀ hk) (fun _ _ => u) (fun _ _ => a) = 0 := by
  rw [rsGammaR_const]; simp [RealArchParam.twist, RealArchParam.gammaR]

theorem rsGammaC_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) (u : ℂ) (a : ZMod 2)
    (u' : ℂ) (k' : ℤ) :
    rsGammaC K (.principal u₁ a₁ u₂ a₂) (fun _ _ => u) (fun _ _ => a) (fun _ _ => u')
        (fun _ _ => k') =
      InfinitePlace.nrComplexPlaces K •
        ({u₁ + u' + (k'.natAbs : ℂ) / 2, u₂ + u' + (k'.natAbs : ℂ) / 2} : Multiset ℂ) := by
  rw [rsGammaC_const, RealArchParam.gammaC_baseChange_twist_principal]
  simp [RealArchParam.twist, RealArchParam.gammaC]

theorem rsGammaC_discrete (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀) (u : ℂ) (a : ZMod 2) (u' : ℂ) (k' : ℤ) :
    rsGammaC K (.discrete u₀ k₀ hk) (fun _ _ => u) (fun _ _ => a) (fun _ _ => u') (fun _ _ => k') =
      InfinitePlace.nrRealPlaces K • ({u₀ + u + (k₀ : ℂ) / 2} : Multiset ℂ) +
        InfinitePlace.nrComplexPlaces K •
          ({u₀ + u' + (((k₀ : ℤ) + k').natAbs : ℂ) / 2,
            u₀ + u' + ((-(k₀ : ℤ) + k').natAbs : ℂ) / 2} : Multiset ℂ) := by
  rw [rsGammaC_const]
  simp [RealArchParam.twist, RealArchParam.gammaC, RealArchParam.baseChange, ComplexArchParam.twist,
    ComplexArchParam.gammaC]

theorem twistedGammaR_archOfParam_dual_const (P : RealArchParam) (u : ℂ) (a : ZMod 2) :
    twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun _ _ => -u) (fun _ _ => a) =
      InfinitePlace.nrRealPlaces K • (P.dual.twist (-u) a).gammaR := by
  simp [twistedGammaR, archOfParamR, Finset.sum_const, Finset.card_univ]

theorem twistedGammaC_archOfParam_dual_const (P : RealArchParam) (u : ℂ) (a : ZMod 2) (u' : ℂ)
    (k' : ℤ) :
    twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
        (fun w hw => (archOfParamC K P w hw).dual) (fun _ _ => -u) (fun _ _ => a) (fun _ _ => -u')
        (fun _ _ => -k') =
      InfinitePlace.nrRealPlaces K • (P.dual.twist (-u) a).gammaC +
        InfinitePlace.nrComplexPlaces K • (P.dual.baseChange.twist (-u') (-k')).gammaC := by
  simp [twistedGammaC, archOfParamR, archOfParamC, Finset.sum_const, Finset.card_univ,
    RealArchParam.gammaC_baseChange_dual_twist]

theorem archRootNumber_archOfParam_const (P : RealArchParam) (u : ℂ) (a : ZMod 2) (u' : ℂ)
    (k' : ℤ) :
    archRootNumber K (archOfParamR K P) (archOfParamC K P) (fun _ _ => u) (fun _ _ => a)
        (fun _ _ => u') (fun _ _ => k') =
      (P.twist u a).epsilonFactor ^ InfinitePlace.nrRealPlaces K *
        (P.baseChange.twist u' k').epsilonFactor ^ InfinitePlace.nrComplexPlaces K := by
  simp [archRootNumber, archOfParamR, archOfParamC, Finset.prod_const, Finset.card_univ]

end Converse

end LanglandsTunnell

end
