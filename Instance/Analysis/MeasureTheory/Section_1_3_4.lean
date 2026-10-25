import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part3


instance PreL1.inst_AddZeroClass {d:ℕ} : AddZeroClass (PreL1 d) := {
  zero := ⟨ 0, ComplexAbsolutelyIntegrable.zero ⟩
  add F G := ⟨ F.f + G.f, F.integrable.add G.integrable ⟩
  zero_add := fun F => by
    apply PreL1.ext
    funext x
    -- Goal: (0 + F).f x = F.f x
    -- (0 + F).f = (⟨0, _⟩ + F).f = (0 : EuclideanSpace' d → ℂ) + F.f
    -- So goal is: (0 + F.f) x = F.f x, i.e., 0 x + F.f x = F.f x
    show (0 : EuclideanSpace' d → ℂ) x + F.f x = F.f x
    simp only [Pi.zero_apply, zero_add]
  add_zero := fun F => by
    apply PreL1.ext
    funext x
    show F.f x + (0 : EuclideanSpace' d → ℂ) x = F.f x
    simp only [Pi.zero_apply, add_zero]
}

instance PreL1.inst_addCommMonoid {d:ℕ} : AddCommMonoid (PreL1 d) := {
  add_assoc := fun F G H => by
    apply PreL1.ext
    funext x
    show (F.f + G.f) x + H.f x = F.f x + (G.f + H.f) x
    simp only [Pi.add_apply, add_assoc]
  add_comm := fun F G => by
    apply PreL1.ext
    funext x
    show F.f x + G.f x = G.f x + F.f x
    ring
  nsmul := nsmulRec
}

instance PreL1.inst_Neg {d:ℕ} : Neg (PreL1 d) := {
  neg F := ⟨ -F.f, F.integrable.of_neg ⟩
}

instance PreL1.inst_Sub {d:ℕ} : Sub (PreL1 d) := {
  sub F G := ⟨ F.f - G.f, F.integrable.sub G.integrable ⟩
}

instance PreL1.inst_module {d:ℕ} : Module ℂ (PreL1 d) := {
  smul c F := ⟨ c • F.f, F.integrable.smul c ⟩
  zero_smul := fun F => by
    apply PreL1.ext
    funext x
    show (0 : ℂ) • F.f x = (0 : EuclideanSpace' d → ℂ) x
    simp only [zero_smul, Pi.zero_apply]
  smul_zero := fun c => by
    apply PreL1.ext
    funext x
    show c • (0 : EuclideanSpace' d → ℂ) x = (0 : EuclideanSpace' d → ℂ) x
    simp only [Pi.zero_apply, smul_zero]
  one_smul := fun F => by
    apply PreL1.ext
    funext x
    show (1 : ℂ) • F.f x = F.f x
    simp only [one_smul]
  mul_smul := fun a b F => by
    apply PreL1.ext
    funext x
    show (a * b) • F.f x = a • (b • F.f x)
    simp only [mul_smul]
  smul_add := fun c F G => by
    apply PreL1.ext
    funext x
    show c • (F.f + G.f) x = (c • F.f + c • G.f) x
    simp only [Pi.add_apply, Pi.smul_apply, smul_add]
  add_smul := fun a b F => by
    apply PreL1.ext
    funext x
    show (a + b) • F.f x = (a • F.f + b • F.f) x
    simp only [Pi.add_apply, Pi.smul_apply, add_smul]
}

