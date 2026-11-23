module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Theorem.UpperHalfPlane.PeriodMap
public import Instance.ModularCurve_PDPairing
public import Abbrev.ModularCurve_PDPairing

public section

set_option autoImplicit false

namespace Matrix.PDPairing

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

section Cores
variable {G : Type*} [Group G] {K : Subgroup G} {C : Type*} [CommGroup C]

public theorem leftTransversals_diff_one [K.FiniteIndex] (S T : K.LeftTransversal) :
    Subgroup.leftTransversals.diff (1 : K →* C) S T = 1 := by
  simp [Subgroup.leftTransversals.diff]


public theorem leftTransversals_diff_mul [K.FiniteIndex] (ϕ ψ : K →* C) (S T : K.LeftTransversal) :
    Subgroup.leftTransversals.diff (ϕ * ψ) S T =
      Subgroup.leftTransversals.diff ϕ S T * Subgroup.leftTransversals.diff ψ S T := by
  simp only [Subgroup.leftTransversals.diff, MonoidHom.mul_apply, Finset.prod_mul_distrib]


public theorem transfer_one [K.FiniteIndex] : MonoidHom.transfer (1 : K →* C) = 1 := by
  ext g
  rw [MonoidHom.transfer_def _ default, leftTransversals_diff_one]
  rfl


public theorem transfer_mul [K.FiniteIndex] (ϕ ψ : K →* C) :
    MonoidHom.transfer (ϕ * ψ) = MonoidHom.transfer ϕ * MonoidHom.transfer ψ := by
  ext g
  rw [MonoidHom.mul_apply, MonoidHom.transfer_def _ default, MonoidHom.transfer_def _ default,
    MonoidHom.transfer_def _ default, leftTransversals_diff_mul]


public theorem toMultiplicativeRight_zero {α β : Type*} [MulOneClass α] [AddCommGroup β] :
    AddMonoidHom.toMultiplicativeRight (0 : Additive α →+ β) = 1 := by
  ext a
  simp


public theorem toMultiplicativeRight_add {α β : Type*} [MulOneClass α] [AddCommGroup β]
    (φ ψ : Additive α →+ β) :
    AddMonoidHom.toMultiplicativeRight (φ + ψ) =
      AddMonoidHom.toMultiplicativeRight φ * AddMonoidHom.toMultiplicativeRight ψ := by
  ext a
  simp [ofAdd_add]


public theorem toAdditiveLeft_one {α β : Type*} [MulOneClass α] [AddCommGroup β] :
    MonoidHom.toAdditiveLeft (1 : α →* Multiplicative β) = 0 := by
  ext a
  simp


public theorem toAdditiveLeft_mul {α β : Type*} [MulOneClass α] [AddCommGroup β]
    (f g : α →* Multiplicative β) :
    MonoidHom.toAdditiveLeft (f * g) = MonoidHom.toAdditiveLeft f + MonoidHom.toAdditiveLeft g := by
  ext a
  simp [toAdd_mul]


public theorem coresAdd_zero (K : Subgroup G) [K.FiniteIndex] {B : Type*} [AddCommGroup B] :
    coresAdd K (0 : Additive ↥K →+ B) = 0 := by
  simp only [coresAdd, toMultiplicativeRight_zero, transfer_one,
    toAdditiveLeft_one]


public theorem coresAdd_add (K : Subgroup G) [K.FiniteIndex] {B : Type*} [AddCommGroup B]
    (φ ψ : Additive ↥K →+ B) : coresAdd K (φ + ψ) = coresAdd K φ + coresAdd K ψ := by
  simp only [coresAdd, toMultiplicativeRight_add, transfer_mul,
    toAdditiveLeft_mul]


public theorem coresAdd_smul (K : Subgroup G) [K.FiniteIndex] {R B : Type*} [Semiring R] [AddCommGroup B]
    [Module R B] (r : R) (φ : Additive ↥K →+ B) : coresAdd K (r • φ) = r • coresAdd K φ := by
  ext g
  simp only [coresAdd, MonoidHom.toAdditiveLeft_apply_apply, AddMonoidHom.smul_apply,
    MonoidHom.transfer_def _ default, Subgroup.leftTransversals.diff, toAdd_prod,
    AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd, Finset.smul_sum]

end Cores

section ConjMats

variable (ℓ d : ℕ)


@[simp] public theorem conjUpperMat_apply_11 (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    (conjUpperMat ℓ A h) 1 1 = A 1 1 := by
  simp [conjUpperMat]


@[simp] public theorem conjUpperMat_apply_10 (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    (conjUpperMat ℓ A h) 1 0 = A 1 0 * ℓ := by
  simp [conjUpperMat]


public theorem conjUpperMat_mul (A B : SL(2, ℤ)) (hA : (ℓ : ℤ) ∣ A 0 1) (hB : (ℓ : ℤ) ∣ B 0 1)
    (hAB : (ℓ : ℤ) ∣ (A * B) 0 1) :
    conjUpperMat ℓ (A * B) hAB = conjUpperMat ℓ A hA * conjUpperMat ℓ B hB := by
  have h1 : A 0 1 / ℓ * (B 1 0 * ℓ) = A 0 1 * B 1 0 := by
    rw [mul_comm (B 1 0) _, ← mul_assoc, Int.ediv_mul_cancel hA]
  have h2 : (A 0 0 * B 0 1 + A 0 1 * B 1 1) / ℓ = A 0 0 * (B 0 1 / ℓ) + A 0 1 / ℓ * B 1 1 := by
    rw [Int.add_ediv_of_dvd_right (Dvd.dvd.mul_right hA _), Int.mul_ediv_assoc _ hB,
      mul_comm (A 0 1) (B 1 1), Int.mul_ediv_assoc _ hA, mul_comm (B 1 1)]
  have h3 : A 1 0 * ℓ * (B 0 1 / ℓ) = A 1 0 * B 0 1 := by
    rw [mul_assoc, Int.mul_ediv_cancel' hB]
  have hmul : ∀ i j, (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := fun i j => by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [conjUpperMat, Matrix.mul_apply, Fin.sum_univ_two, hmul, h2]
  · exact h1.symm
  · ring
  · exact h3.symm


public theorem conjLowerMat_mul (A B : SL(2, ℤ)) (hA : (d : ℤ) ∣ A 1 0) (hB : (d : ℤ) ∣ B 1 0)
    (hAB : (d : ℤ) ∣ (A * B) 1 0) :
    conjLowerMat d (A * B) hAB = conjLowerMat d A hA * conjLowerMat d B hB := by
  have h1 : A 0 1 * d * (B 1 0 / d) = A 0 1 * B 1 0 := by
    rw [mul_assoc, Int.mul_ediv_cancel' hB]
  have h2 : (A 1 0 * B 0 0 + A 1 1 * B 1 0) / d = A 1 0 / d * B 0 0 + A 1 1 * (B 1 0 / d) := by
    rw [Int.add_ediv_of_dvd_right (Dvd.dvd.mul_left hB _), Int.mul_ediv_assoc _ hB,
      mul_comm (A 1 0) (B 0 0), Int.mul_ediv_assoc _ hA, mul_comm (B 0 0)]
  have h3 : A 1 0 / d * (B 0 1 * d) = A 1 0 * B 0 1 := by
    rw [mul_comm (B 0 1) _, ← mul_assoc, Int.ediv_mul_cancel hA]
  have hmul : ∀ i j, (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := fun i j => by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [conjLowerMat, Matrix.mul_apply, Fin.sum_univ_two, hmul, h2]
  all_goals first | exact h1.symm | exact h3.symm | ring


public theorem conjLowerMat_conjUpperMat [NeZero d] (A : SL(2, ℤ)) (hb : (d : ℤ) ∣ A 0 1)
    (hc : (d : ℤ) ∣ (conjUpperMat d A hb) 1 0) : conjLowerMat d (conjUpperMat d A hb) hc = A := by
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [conjLowerMat, conjUpperMat, Int.ediv_mul_cancel hb, Int.mul_ediv_cancel _ hd]

end ConjMats

section Gamma0Legs

variable (M M' d : ℕ)


public theorem exists_eq0 (hMM' : M ∣ M') (hdd : d ∣ M' / M) : ∃ e : ℕ, M' = M * (d * e) := by
  obtain ⟨e, he⟩ := hdd
  refine ⟨e, ?_⟩
  rw [← he, Nat.mul_div_cancel' hMM']


public theorem dvd_entry0 (hMM' : M ∣ M') (hdd : d ∣ M' / M) (γ : ↥(Gamma0 M')) :
    (d : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := by
  have hM' : ((M' : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.2)
  obtain ⟨e, he⟩ := exists_eq0 M M' d hMM' hdd
  refine dvd_trans ?_ hM'
  rw [he]
  push_cast
  exact Dvd.intro_left ((M : ℤ) * e) (by ring)


public theorem conjLowerMat_mem0 [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) (γ : ↥(Gamma0 M')) :
    conjLowerMat d (γ : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd γ) ∈ Gamma0 M := by
  have hM' : ((M' : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.2)
  obtain ⟨e, he⟩ := exists_eq0 M M' d hMM' hdd
  obtain ⟨t, ht⟩ := hM'
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hquot : (γ : SL(2, ℤ)) 1 0 / (d : ℤ) = (M : ℤ) * (e * t) := by
    apply Int.ediv_eq_of_eq_mul_right hd0
    rw [ht, he]
    push_cast
    ring
  rw [Gamma0_mem]
  show (((!![(γ : SL(2, ℤ)) 0 0, (γ : SL(2, ℤ)) 0 1 * d; (γ : SL(2, ℤ)) 1 0 / d, (γ : SL(2, ℤ)) 1 1]
    : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M) = 0
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [hquot]
  push_cast
  rw [ZMod.natCast_self, zero_mul]


public theorem Gamma_subgroupOf_le_range_iotaDeg0 [NeZero M'] [NeZero d]
    (hMM' : M ∣ M') (hdd : d ∣ M' / M) :
    (Gamma (M' * d)).subgroupOf (Gamma0 M) ≤ (iotaDeg0 M M' d hMM' hdd).range := by
  intro γ hγ
  rw [Subgroup.mem_subgroupOf, Gamma_mem] at hγ
  obtain ⟨_, h01, h10, _⟩ := hγ
  have hMd : ((M' * d : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h01
  have hMd' : ((M' * d : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  have hb : (d : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 := dvd_trans (by push_cast; exact Dvd.intro_left _ rfl) hMd
  set A : SL(2, ℤ) := conjUpperMat d (γ : SL(2, ℤ)) hb with hAdef
  have hA0 : A ∈ Gamma0 M' := by
    rw [Gamma0_mem]
    have : A 1 0 = (γ : SL(2, ℤ)) 1 0 * d := by simp [hAdef, conjUpperMat]
    rw [this, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Dvd.dvd.mul_right (dvd_trans (by push_cast; exact Dvd.intro _ rfl) hMd') _
  have hc : (d : ℤ) ∣ (conjUpperMat d (γ : SL(2, ℤ)) hb) 1 0 := by
    rw [conjUpperMat_apply_10]
    exact dvd_mul_left _ _
  refine ⟨⟨A, hA0⟩, Subtype.ext ?_⟩
  exact conjLowerMat_conjUpperMat d (γ : SL(2, ℤ)) hb hc


public theorem iotaDeg0_injective [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) :
    Function.Injective (iotaDeg0 M M' d hMM' hdd) := by
  intro γ δ hγδ
  have hmat : conjLowerMat d (γ : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd γ) =
      conjLowerMat d (δ : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd δ) := congrArg Subtype.val hγδ
  have e : ∀ i j, (conjLowerMat d (γ : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd γ)) i j =
      (conjLowerMat d (δ : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd δ)) i j := fun i j => by rw [hmat]
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [conjLowerMat] using e 0 0
  · have h01 := e 0 1
    simp only [conjLowerMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h01
    exact mul_right_cancel₀ hd h01
  · have h10 := e 1 0
    simp only [conjLowerMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h10
    calc (γ : SL(2, ℤ)) 1 0
        = d * ((γ : SL(2, ℤ)) 1 0 / d) := (Int.mul_ediv_cancel' (dvd_entry0 M M' d hMM' hdd γ)).symm
      _ = d * ((δ : SL(2, ℤ)) 1 0 / d) := by rw [h10]
      _ = (δ : SL(2, ℤ)) 1 0 := Int.mul_ediv_cancel' (dvd_entry0 M M' d hMM' hdd δ)
  · simpa [conjLowerMat] using e 1 1


@[simp]
public theorem mem_Gamma0Upper {ℓ : ℕ} {A : SL(2, ℤ)} : A ∈ Gamma0Upper ℓ ↔ (A 0 1 : ZMod ℓ) = 0 :=
  Iff.rfl


public theorem Gamma0Upper_isCongruenceSubgroup (ℓ : ℕ) [NeZero ℓ] :
    IsCongruenceSubgroup (Gamma0Upper ℓ) := by
  refine ⟨ℓ, NeZero.ne _, fun A hA => ?_⟩
  rw [mem_Gamma0Upper]
  exact (Gamma_mem.mp hA).2.1

variable (ℓ : ℕ)


public theorem dvd_of_mem_Gamma0HUpper (γ : ↥(Gamma0HUpper M ℓ)) :
    (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 := by
  have h : ((γ : ↥(Gamma0 M)) : SL(2, ℤ)) ∈ Gamma0Upper ℓ := Subgroup.mem_subgroupOf.mp γ.2
  rw [mem_Gamma0Upper] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h


public theorem conjUpperMat_mem0 (γ : ↥(Gamma0HUpper M ℓ)) :
    conjUpperMat ℓ (γ : SL(2, ℤ)) (dvd_of_mem_Gamma0HUpper M ℓ γ) ∈ Gamma0 M := by
  rw [Gamma0_mem, conjUpperMat_apply_10, Int.cast_mul,
    Gamma0_mem.mp (γ : ↥(Gamma0 M)).2, zero_mul]


public theorem heckeT0_apply [NeZero ℓ] (φ : Additive ↥(Gamma0 M) →+ A) :
    heckeT0 M ℓ A φ =
      MonoidHom.toAdditiveLeft
        (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL0 M ℓ))) :=
  rfl

end Gamma0Hecke

section Prim
variable {Φ : Type*} [Group Φ] {R : Type*} [CommRing R]


public theorem omega_one_left (φ ψ : Additive Φ →+ R) (g : Φ) : omega φ ψ 1 g = 0 := by
  simp [omega]


public theorem omega_one_right (φ ψ : Additive Φ →+ R) (g : Φ) : omega φ ψ g 1 = 0 := by
  simp [omega]


public theorem omega_inv_self (φ ψ : Additive Φ →+ R) (g : Φ) : omega φ ψ g⁻¹ g = 0 := by
  simp only [omega, ofMul_inv, map_neg]
  ring


public theorem omega_self_inv (φ ψ : Additive Φ →+ R) (g : Φ) : omega φ ψ g g⁻¹ = 0 := by
  simp only [omega, ofMul_inv, map_neg]
  ring


public theorem omega_cocycle (φ ψ : Additive Φ →+ R) (g h k : Φ) :
    omega φ ψ g h + omega φ ψ (g * h) k = omega φ ψ h k + omega φ ψ g (h * k) := by
  simp only [omega, ofMul_mul, map_add]
  ring


public theorem omega_swap (φ ψ : Additive Φ →+ R) (g h : Φ) : omega ψ φ g h = - omega φ ψ g h := by
  simp only [omega]
  ring


public theorem mul_def (x y : CentralExt φ ψ) :
    x * y = (x.1 + y.1 - omega φ ψ x.2 y.2, x.2 * y.2) := rfl


public theorem one_def : (1 : CentralExt φ ψ) = ((0 : R), (1 : Φ)) := rfl


public theorem inv_def (x : CentralExt φ ψ) : x⁻¹ = (-x.1, x.2⁻¹) := rfl


@[simp] public theorem snd_apply (x : CentralExt φ ψ) : snd φ ψ x = x.2 := rfl

end CentralExt

variable [IsFreeGroup Φ]


public theorem snd_comp_sect (φ ψ : Additive Φ →+ R) :
    (CentralExt.snd φ ψ).comp (sect φ ψ) = MonoidHom.id Φ := by
  apply IsFreeGroup.ext_hom
  intro a
  simp [sect]


@[simp] public theorem sect_snd (φ ψ : Additive Φ →+ R) (g : Φ) : (sect φ ψ g).2 = g := by
  have h := congrArg (fun f : Φ →* Φ => f g) (snd_comp_sect φ ψ)
  simpa using h


public theorem hPrim_mul (φ ψ : Additive Φ →+ R) (g g' : Φ) :
    hPrim φ ψ (g * g') = hPrim φ ψ g + hPrim φ ψ g' - omega φ ψ g g' := by
  have h := map_mul (sect φ ψ) g g'
  have h1 := congrArg Prod.fst h
  simp only [CentralExt.mul_def, sect_snd] at h1
  exact h1


public theorem hPrim_one (φ ψ : Additive Φ →+ R) : hPrim φ ψ 1 = 0 := by
  have h := map_one (sect φ ψ)
  exact congrArg Prod.fst h


@[simp] public theorem CentralExt.lift_apply (φ ψ : Additive Φ →+ R) (H : Φ → R)
    (hH : ∀ g g', H (g * g') = H g + H g' - omega φ ψ g g') (g : Φ) :
    CentralExt.lift φ ψ H hH g = (H g, g) := rfl


public theorem hPrim_unique (φ ψ : Additive Φ →+ R) (H : Φ → R)
    (hH : ∀ g g', H (g * g') = H g + H g' - omega φ ψ g g')
    (h0 : ∀ a : IsFreeGroup.Generators Φ, H (IsFreeGroup.of a) = 0) (g : Φ) : H g = hPrim φ ψ g := by
  have key : CentralExt.lift φ ψ H hH = sect φ ψ := by
    apply IsFreeGroup.ext_hom
    intro a
    rw [CentralExt.lift_apply, h0 a]
    simp [sect]
  exact congrArg Prod.fst (congrArg (fun f : Φ →* CentralExt φ ψ => f g) key)


public theorem hPrim_of (φ ψ : Additive Φ →+ R) (a : IsFreeGroup.Generators Φ) : hPrim φ ψ (IsFreeGroup.of a) = 0 := by
  simp [hPrim, sect]

omit [IsFreeGroup Φ] in

public theorem omega_add_left (φ₁ φ₂ ψ : Additive Φ →+ R) (g g' : Φ) :
    omega (φ₁ + φ₂) ψ g g' = omega φ₁ ψ g g' + omega φ₂ ψ g g' := by
  simp only [omega, AddMonoidHom.add_apply]
  ring

omit [IsFreeGroup Φ] in

public theorem omega_smul_left (r : R) (φ ψ : Additive Φ →+ R) (g g' : Φ) :
    omega (r • φ) ψ g g' = r * omega φ ψ g g' := by
  simp only [omega, AddMonoidHom.smul_apply, smul_eq_mul]
  ring


public theorem hPrim_add_left (φ₁ φ₂ ψ : Additive Φ →+ R) (g : Φ) :
    hPrim (φ₁ + φ₂) ψ g = hPrim φ₁ ψ g + hPrim φ₂ ψ g := by
  symm
  refine hPrim_unique (φ₁ + φ₂) ψ (fun g => hPrim φ₁ ψ g + hPrim φ₂ ψ g) ?_ ?_ g
  · intro g g'
    rw [hPrim_mul, hPrim_mul, omega_add_left]
    ring
  · intro a
    rw [hPrim_of, hPrim_of, add_zero]


public theorem hPrim_smul_left (r : R) (φ ψ : Additive Φ →+ R) (g : Φ) :
    hPrim (r • φ) ψ g = r * hPrim φ ψ g := by
  symm
  refine hPrim_unique (r • φ) ψ (fun g => r * hPrim φ ψ g) ?_ ?_ g
  · intro g g'
    rw [hPrim_mul, omega_smul_left]
    ring
  · intro a
    rw [hPrim_of, mul_zero]


public theorem hPrim_swap (φ ψ : Additive Φ →+ R) (g : Φ) : hPrim ψ φ g = - hPrim φ ψ g := by
  refine (hPrim_unique ψ φ (fun g => - hPrim φ ψ g) ?_ ?_ g).symm
  · intro g g'
    rw [hPrim_mul, omega_swap]
    ring
  · intro a
    rw [hPrim_of, neg_zero]

end Prim

section Cusps

open MulAction

variable (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] {R : Type*} [CommRing R]


public theorem cuspSum_add (f g : Φ → R) : cuspSum Φ (f + g) = cuspSum Φ f + cuspSum Φ g := by
  simp [cuspSum, Finset.sum_add_distrib]


public theorem cuspSum_smul (r : R) (f : Φ → R) : cuspSum Φ (r • f) = r * cuspSum Φ f := by
  simp [cuspSum, Finset.mul_sum]


public theorem pairZFun_add_left (φ₁ φ₂ ψ : Additive ↥(Gamma0 N) →+ ℤ) :
    pairZFun N (φ₁ + φ₂) ψ = pairZFun N φ₁ ψ + pairZFun N φ₂ ψ := by
  have h : hPrim (resInf (Gamma 4) (Gamma0 N) (φ₁ + φ₂)) (resInf (Gamma 4) (Gamma0 N) ψ) =
      hPrim (resInf (Gamma 4) (Gamma0 N) φ₁) (resInf (Gamma 4) (Gamma0 N) ψ) +
        hPrim (resInf (Gamma 4) (Gamma0 N) φ₂) (resInf (Gamma 4) (Gamma0 N) ψ) := by
    funext g
    rw [Pi.add_apply, ← hPrim_add_left]
    rfl
  rw [pairZFun, pairZFun, pairZFun, h, cuspSum_add, mul_add]


public theorem pairZFun_smul_left (r : ℤ) (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) :
    pairZFun N (r • φ) ψ = r * pairZFun N φ ψ := by
  have h : hPrim (resInf (Gamma 4) (Gamma0 N) (r • φ)) (resInf (Gamma 4) (Gamma0 N) ψ) =
      r • hPrim (resInf (Gamma 4) (Gamma0 N) φ) (resInf (Gamma 4) (Gamma0 N) ψ) := by
    funext g
    rw [Pi.smul_apply, smul_eq_mul, ← hPrim_smul_left]
    rfl
  rw [pairZFun, pairZFun, h, cuspSum_smul]
  ring


public theorem pairZFun_swap (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) : pairZFun N ψ φ = - pairZFun N φ ψ := by
  have h : hPrim (resInf (Gamma 4) (Gamma0 N) ψ) (resInf (Gamma 4) (Gamma0 N) φ) =
      (-1 : ℤ) • hPrim (resInf (Gamma 4) (Gamma0 N) φ) (resInf (Gamma 4) (Gamma0 N) ψ) := by
    funext g
    rw [Pi.smul_apply, smul_eq_mul, hPrim_swap]
    ring
  rw [pairZFun, pairZFun, h, cuspSum_smul]
  ring


public theorem pairZFun_add_right (φ ψ₁ ψ₂ : Additive ↥(Gamma0 N) →+ ℤ) :
    pairZFun N φ (ψ₁ + ψ₂) = pairZFun N φ ψ₁ + pairZFun N φ ψ₂ := by
  rw [pairZFun_swap, pairZFun_add_left, neg_add, ← pairZFun_swap, ← pairZFun_swap]


public theorem pairZFun_smul_right (r : ℤ) (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) :
    pairZFun N φ (r • ψ) = r * pairZFun N φ ψ := by
  rw [pairZFun_swap, pairZFun_smul_left, pairZFun_swap]
  ring


@[simp] public theorem pairZ_apply (x y : parabolicHoms ℤ (Gamma0 N) ℤ) :
    pairZ N x y = pairZFun N (x : Additive ↥(Gamma0 N) →+ ℤ) (y : Additive ↥(Gamma0 N) →+ ℤ) := rfl

end LevelZ

end Matrix.PDPairing
