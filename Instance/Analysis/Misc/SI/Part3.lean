import Mathlib
import Theorem.Analysis.Misc.UnitsSystem.Part23
import Mathlib.Algebra.Group.MinimalAxioms
import Theorem.Analysis.Misc.SI.Part2


instance SI_dimensions.instAddGroup : AddGroup SI_dimensions :=
AddGroup.ofLeftAxioms
  (by intros; simp_rw [HAdd.hAdd, Add.add]; simp [add_assoc])
  (by intros; simp_rw [HAdd.hAdd, Add.add, OfNat.ofNat, Zero.zero]; simp)
  (by intros; simp_rw [Neg.neg, HAdd.hAdd, Add.add, OfNat.ofNat, Zero.zero]; simp)

instance SI_dimensions.instAddCommGroup : AddCommGroup SI_dimensions where
  add_comm d₁ d₂ := by
    simp_rw [HAdd.hAdd, Add.add]; simp [add_comm]

instance SI_dimensions.instSMul : SMul ℚ SI_dimensions where
  smul q d := ⟨q * d.units_length, q * d.units_mass, q * d.units_time, q * d.units_current,
                q * d.units_temperature, q * d.units_amount, q * d.units_intensity⟩

instance SI_dimensions.instModule : Module ℚ SI_dimensions where
  one_smul d := by
    ext <;> simp [HSMul.hSMul, SMul.smul]
  mul_smul q₁ q₂ d := by
    ext <;> simp [HSMul.hSMul, SMul.smul, mul_assoc]
  smul_add q d₁ d₂ := by
    ext <;> simp [HSMul.hSMul, SMul.smul, HAdd.hAdd, Add.add] <;> simp [Rat.add_eq, mul_add]
  smul_zero q := by
    ext <;> simp [HSMul.hSMul, SMul.smul, zero_eq]
  add_smul d₁ d₂ q := by
    ext <;> simp [HAdd.hAdd, Add.add, HSMul.hSMul, SMul.smul] <;> simp [Rat.add_eq, add_mul]
  zero_smul d := by
    ext <;> simp [HSMul.hSMul, SMul.smul, zero_eq]

