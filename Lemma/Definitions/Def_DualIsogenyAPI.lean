import Mathlib

set_option autoImplicit false

namespace AddMonoidHom

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

structure IsDualPair (φ : A →+ B) (ψ : B →+ A) (n : ℤ) : Prop where

  comp_left : ∀ a, ψ (φ a) = n • a

  comp_right : ∀ b, φ (ψ b) = n • b

theorem IsDualPair.symm {φ : A →+ B} {ψ : B →+ A} {n : ℤ} (h : IsDualPair φ ψ n) :
    IsDualPair ψ φ n :=
  ⟨h.comp_right, h.comp_left⟩

theorem isDualPair_comm {φ : A →+ B} {ψ : B →+ A} {n : ℤ} :
    IsDualPair φ ψ n ↔ IsDualPair ψ φ n :=
  ⟨IsDualPair.symm, IsDualPair.symm⟩

theorem IsDualPair.comp {φ' : A →+ B} {φ : B →+ A} {m : ℤ} {ψ' : B →+ C} {ψ : C →+ B}
    {n : ℤ} (hφ : IsDualPair φ' φ m) (hψ : IsDualPair ψ' ψ n) :
    IsDualPair (ψ'.comp φ') (φ.comp ψ) (m * n) := by
  refine ⟨fun a => ?_, fun c => ?_⟩
  · show φ (ψ (ψ' (φ' a))) = (m * n) • a
    rw [hψ.comp_left, map_zsmul, hφ.comp_left, mul_zsmul']
  · show ψ' (φ' (φ (ψ c))) = (m * n) • c
    rw [hφ.comp_right, map_zsmul, hψ.comp_right, mul_zsmul]

theorem isDualPair_intCast (m : ℤ) :
    IsDualPair (A := A) (B := A) (m : AddMonoid.End A) (m : AddMonoid.End A) (m ^ 2) := by
  have key : ∀ a : A, (m : AddMonoid.End A) ((m : AddMonoid.End A) a) = m ^ 2 • a := by
    intro a
    have h : (m : AddMonoid.End A) ((m : AddMonoid.End A) a)
        = ((m : AddMonoid.End A) * (m : AddMonoid.End A)) a := rfl
    rw [h, ← Int.cast_mul, AddMonoid.End.intCast_apply, sq]
  exact ⟨key, key⟩

theorem isDualPair_id_one : IsDualPair (id A) (id A) 1 :=
  ⟨fun a => (one_zsmul a).symm, fun a => (one_zsmul a).symm⟩

theorem IsDualPair.left_unique_of_surjective {φ : A →+ B} {ψ : B →+ A} {n : ℤ}
    (h : IsDualPair φ ψ n) (hφ : Function.Surjective φ) {ψ' : B →+ A}
    (hψ' : ∀ a, ψ' (φ a) = n • a) : ψ' = ψ := by
  ext b
  obtain ⟨a, rfl⟩ := hφ b
  rw [hψ', h.comp_left]

theorem IsDualPair.right_unique_of_injective {φ : A →+ B} {ψ : B →+ A} {n : ℤ}
    (h : IsDualPair φ ψ n) (hφ : Function.Injective φ) {ψ' : B →+ A}
    (hψ' : ∀ b, φ (ψ' b) = n • b) : ψ' = ψ := by
  ext b; exact hφ (by rw [hψ', h.comp_right])

theorem IsDualPair.ker_le_torsion_left {φ : A →+ B} {ψ : B →+ A} {n : ℤ}
    (h : IsDualPair φ ψ n) {b : B} (hb : ψ b = 0) : n • b = 0 := by
  rw [← h.comp_right b, hb, map_zero]

theorem IsDualPair.ker_le_torsion_right {φ : A →+ B} {ψ : B →+ A} {n : ℤ}
    (h : IsDualPair φ ψ n) {a : A} (ha : φ a = 0) : n • a = 0 :=
  h.symm.ker_le_torsion_left ha

theorem IsDualPair.nsmul_mem_range_left {φ : A →+ B} {ψ : B →+ A} {n : ℤ}
    (h : IsDualPair φ ψ n) (a : A) : n • a ∈ Set.range ψ :=
  ⟨φ a, h.comp_left a⟩

theorem IsDualPair.surjective_of_divisible {φ : A →+ B} {ψ : B →+ A} {n : ℤ}
    (h : IsDualPair φ ψ n) (hdiv : ∀ a : A, ∃ a', n • a' = a) :
    Function.Surjective ψ := by
  intro a; obtain ⟨a', ha'⟩ := hdiv a; exact ⟨φ a', by rw [h.comp_left, ha']⟩

theorem IsDualPair.neg {φ : A →+ B} {ψ : B →+ A} {n : ℤ} (h : IsDualPair φ ψ n) :
    IsDualPair (-φ) (-ψ) n :=
  ⟨fun a => by simp [h.comp_left], fun b => by simp [h.comp_right]⟩

end AddMonoidHom

namespace AddMonoid.End

variable {A : Type*} [AddCommGroup A]

structure DualEndData (φ : AddMonoid.End A) where

  dual : AddMonoid.End A

  trace : ℤ

  norm : ℤ

  add_dual : φ + dual = (trace : AddMonoid.End A)

  mul_dual : φ * dual = (norm : AddMonoid.End A)

  dual_mul : dual * φ = (norm : AddMonoid.End A)

namespace DualEndData

variable {φ : AddMonoid.End A}

theorem isDualPair (D : DualEndData φ) :
    AddMonoidHom.IsDualPair (A := A) (B := A) φ D.dual D.norm := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · have h := DFunLike.congr_fun D.dual_mul a
    rwa [AddMonoid.End.intCast_apply] at h
  · have h := DFunLike.congr_fun D.mul_dual a
    rwa [AddMonoid.End.intCast_apply] at h

theorem commute (D : DualEndData φ) : Commute φ D.dual := by
  unfold Commute SemiconjBy; rw [D.mul_dual, D.dual_mul]

theorem dual_eq (D : DualEndData φ) : D.dual = (D.trace : AddMonoid.End A) - φ := by
  rw [← D.add_dual, add_sub_cancel_left]

theorem charPoly (D : DualEndData φ) :
    φ * φ - (D.trace : AddMonoid.End A) * φ + (D.norm : AddMonoid.End A) = 0 := by
  have h := D.dual_mul
  rw [D.dual_eq, sub_mul] at h
  rw [← h]; abel

theorem add_dual_apply (D : DualEndData φ) (a : A) :
    φ a + D.dual a = D.trace • a := by
  have h : (φ + D.dual) a = (D.trace : AddMonoid.End A) a := by rw [D.add_dual]
  rwa [AddMonoid.End.intCast_apply] at h

theorem charPoly_apply (D : DualEndData φ) (a : A) :
    φ (φ a) - D.trace • φ a + D.norm • a = 0 := by

  have h1 := D.isDualPair.comp_left a
  have h2 := D.add_dual_apply (φ a)
  rw [← h1, ← h2, sub_add_cancel_left]; exact neg_add_cancel _

def symm (D : DualEndData φ) : DualEndData D.dual where
  dual := φ
  trace := D.trace
  norm := D.norm
  add_dual := by rw [← D.add_dual, add_comm]
  mul_dual := D.dual_mul
  dual_mul := D.mul_dual

@[simp] theorem symm_dual (D : DualEndData φ) : D.symm.dual = φ := rfl
@[simp] theorem symm_trace (D : DualEndData φ) : D.symm.trace = D.trace := rfl
@[simp] theorem symm_norm (D : DualEndData φ) : D.symm.norm = D.norm := rfl

private theorem intLin_apply (a b : ℤ) (ψ : AddMonoid.End A) (x : A) :
    ((a : AddMonoid.End A) + (b : AddMonoid.End A) * ψ) x = a • x + b • ψ x := by
  show (a : AddMonoid.End A) x + (b : AddMonoid.End A) (ψ x) = _
  rw [AddMonoid.End.intCast_apply, AddMonoid.End.intCast_apply]

theorem dual_charPoly (D : DualEndData φ) :
    D.dual * D.dual - (D.trace : AddMonoid.End A) * D.dual
      + (D.norm : AddMonoid.End A) = 0 :=
  D.symm.charPoly

theorem intLinComb_mul_dual (D : DualEndData φ) (a b : ℤ) :
    ((a : AddMonoid.End A) + (b : AddMonoid.End A) * φ)
      * ((a : AddMonoid.End A) + (b : AddMonoid.End A) * D.dual)
      = ((a ^ 2 + D.trace * a * b + D.norm * b ^ 2 : ℤ) : AddMonoid.End A) := by

  ext x
  show ((a : AddMonoid.End A) + b * φ)
      (((a : AddMonoid.End A) + b * D.dual) x)
    = ((a ^ 2 + D.trace * a * b + D.norm * b ^ 2 : ℤ) : AddMonoid.End A) x
  rw [intLin_apply, intLin_apply, AddMonoid.End.intCast_apply,
    map_add, map_zsmul, map_zsmul]
  have hcr : φ (D.dual x) = D.norm • x := D.isDualPair.comp_right x
  have hsum := D.add_dual_apply x
  calc a • (a • x + b • D.dual x) + b • (a • φ x + b • φ (D.dual x))
      = (a * a) • x + (a * b) • D.dual x + ((b * a) • φ x + (b * b) • φ (D.dual x)) := by
        simp only [zsmul_add, ← mul_zsmul]
    _ = (a * a) • x + (a * b) • (φ x + D.dual x) + (b * b) • φ (D.dual x) := by
        rw [zsmul_add, mul_comm b a]; abel
    _ = (a ^ 2 + D.trace * a * b + D.norm * b ^ 2) • x := by
        rw [hcr, hsum, ← mul_zsmul, ← mul_zsmul, ← add_zsmul, ← add_zsmul]
        congr 1; ring

def intLinComb (D : DualEndData φ) (a b : ℤ) :
    DualEndData ((a : AddMonoid.End A) + (b : AddMonoid.End A) * φ) where
  dual := (a : AddMonoid.End A) + (b : AddMonoid.End A) * D.dual
  trace := 2 * a + D.trace * b
  norm := a ^ 2 + D.trace * a * b + D.norm * b ^ 2
  add_dual := by
    have h : (a : AddMonoid.End A) + b * φ + ((a : AddMonoid.End A) + b * D.dual)
        = (a : AddMonoid.End A) + (a : AddMonoid.End A) + b * (φ + D.dual) := by
      rw [mul_add]; abel
    rw [h, D.add_dual]
    ext x
    show (a : AddMonoid.End A) x + (a : AddMonoid.End A) x
        + ((b : AddMonoid.End A) * (D.trace : AddMonoid.End A)) x
      = ((2 * a + D.trace * b : ℤ) : AddMonoid.End A) x
    rw [show ((b : AddMonoid.End A) * (D.trace : AddMonoid.End A)) x
          = (b : AddMonoid.End A) ((D.trace : AddMonoid.End A) x) from rfl,
      AddMonoid.End.intCast_apply, AddMonoid.End.intCast_apply, AddMonoid.End.intCast_apply,
      AddMonoid.End.intCast_apply, ← add_zsmul, ← mul_zsmul, ← add_zsmul]
    congr 1; ring
  mul_dual := D.intLinComb_mul_dual a b
  dual_mul := D.symm.intLinComb_mul_dual a b

@[simp] theorem intLinComb_norm (D : DualEndData φ) (a b : ℤ) :
    (D.intLinComb a b).norm = a ^ 2 + D.trace * a * b + D.norm * b ^ 2 := rfl

@[simp] theorem intLinComb_trace (D : DualEndData φ) (a b : ℤ) :
    (D.intLinComb a b).trace = 2 * a + D.trace * b := rfl

@[simp] theorem intLinComb_dual (D : DualEndData φ) (a b : ℤ) :
    (D.intLinComb a b).dual = (a : AddMonoid.End A) + (b : AddMonoid.End A) * D.dual := rfl

theorem intLinComb_disc (D : DualEndData φ) (a b : ℤ) :
    (D.intLinComb a b).trace ^ 2 - 4 * (D.intLinComb a b).norm
      = b ^ 2 * (D.trace ^ 2 - 4 * D.norm) := by
  simp only [intLinComb_trace, intLinComb_norm]; ring

theorem intLinComb_disc_neg (D : DualEndData φ) {a b : ℤ} (hb : b ≠ 0)
    (hD : D.trace ^ 2 < 4 * D.norm) :
    (D.intLinComb a b).trace ^ 2 < 4 * (D.intLinComb a b).norm := by
  have hkey := D.intLinComb_disc a b
  have hbsq : (0 : ℤ) < b ^ 2 := by positivity
  nlinarith

end DualEndData

def DualEndData.ofCharPoly (φ : AddMonoid.End A) (t n : ℤ)
    (hchar : φ * φ - (t : AddMonoid.End A) * φ + (n : AddMonoid.End A) = 0) :
    DualEndData φ where
  dual := (t : AddMonoid.End A) - φ
  trace := t
  norm := n
  add_dual := by abel
  mul_dual := by
    have hc : φ * (t : AddMonoid.End A) = (t : AddMonoid.End A) * φ :=
      (Int.cast_commute t φ).eq.symm
    have := hchar; rw [mul_sub, hc, ← sub_eq_zero,
      show (t : AddMonoid.End A) * φ - φ * φ - (n : AddMonoid.End A)
        = -(φ * φ - (t : AddMonoid.End A) * φ + (n : AddMonoid.End A)) by abel,
      this, neg_zero]
  dual_mul := by
    have := hchar; rw [sub_mul, ← sub_eq_zero,
      show (t : AddMonoid.End A) * φ - φ * φ - (n : AddMonoid.End A)
        = -(φ * φ - (t : AddMonoid.End A) * φ + (n : AddMonoid.End A)) by abel,
      this, neg_zero]

@[simp] theorem DualEndData.ofCharPoly_trace (φ : AddMonoid.End A) (t n : ℤ) (h) :
    (DualEndData.ofCharPoly φ t n h).trace = t := rfl

@[simp] theorem DualEndData.ofCharPoly_norm (φ : AddMonoid.End A) (t n : ℤ) (h) :
    (DualEndData.ofCharPoly φ t n h).norm = n := rfl

@[simp] theorem DualEndData.ofCharPoly_dual (φ : AddMonoid.End A) (t n : ℤ) (h) :
    (DualEndData.ofCharPoly φ t n h).dual = (t : AddMonoid.End A) - φ := rfl

def dualEndData_intCast (m : ℤ) : DualEndData (A := A) (m : AddMonoid.End A) where
  dual := (m : AddMonoid.End A)
  trace := 2 * m
  norm := m ^ 2
  add_dual := by push_cast; noncomm_ring
  mul_dual := by rw [← Int.cast_mul, ← sq]
  dual_mul := by rw [← Int.cast_mul, ← sq]

@[simp] theorem dualEndData_intCast_norm (m : ℤ) :
    (dualEndData_intCast (A := A) m).norm = m ^ 2 := rfl

@[simp] theorem dualEndData_intCast_trace (m : ℤ) :
    (dualEndData_intCast (A := A) m).trace = 2 * m := rfl

@[simp] theorem dualEndData_intCast_dual (m : ℤ) :
    (dualEndData_intCast (A := A) m).dual = (m : AddMonoid.End A) := rfl

end AddMonoid.End

section NamedResiduals

variable {A : Type*} [AddCommGroup A]

def DualIsogenyExistence (S : Subring (AddMonoid.End A)) : Prop :=
  ∀ φ ∈ S, ∃ D : AddMonoid.End.DualEndData φ, D.dual ∈ S ∧ 0 ≤ D.norm

def DualAdditivityResidual (S : Subring (AddMonoid.End A)) : Prop :=
  ∀ φ ∈ S, ∀ ψ ∈ S, ∀ Dφ : AddMonoid.End.DualEndData φ, ∀ Dψ : AddMonoid.End.DualEndData ψ,
    ∃ D : AddMonoid.End.DualEndData (φ + ψ), D.dual = Dφ.dual + Dψ.dual

theorem dualIsogenyExistence_bot :
    DualIsogenyExistence (⊥ : Subring (AddMonoid.End A)) := by
  intro φ hφ
  obtain ⟨m, rfl⟩ := Subring.mem_bot.mp hφ
  exact ⟨AddMonoid.End.dualEndData_intCast m, Subring.mem_bot.mpr ⟨m, rfl⟩, sq_nonneg m⟩

end NamedResiduals

section SatGates

private theorem one_charPoly_int :
    (1 : AddMonoid.End ℤ) * 1 - ((2 : ℤ) : AddMonoid.End ℤ) * 1
      + ((1 : ℤ) : AddMonoid.End ℤ) = 0 := by
  norm_num

theorem gate_intLinComb_norm_at_one :

    ((AddMonoid.End.DualEndData.ofCharPoly (A := ℤ) 1 2 1
      one_charPoly_int).intLinComb 1 2).norm = 9 := by
  simp only [AddMonoid.End.DualEndData.intLinComb_norm,
    AddMonoid.End.DualEndData.ofCharPoly_trace, AddMonoid.End.DualEndData.ofCharPoly_norm]
  decide

theorem gate_dualEndData_intCast_three :
    (AddMonoid.End.dualEndData_intCast (A := ℤ) 3).norm = 9
    ∧ (AddMonoid.End.dualEndData_intCast (A := ℤ) 3).trace = 6 := ⟨rfl, rfl⟩

theorem gate_intLinComb_disc_scaling :
    ((AddMonoid.End.DualEndData.ofCharPoly (A := ℤ) 1 2 1
      one_charPoly_int).intLinComb 0 2).trace ^ 2
        - 4 * ((AddMonoid.End.DualEndData.ofCharPoly (A := ℤ) 1 2 1
          one_charPoly_int).intLinComb 0 2).norm = 2 ^ 2 * (2 ^ 2 - 4 * 1) := by
  rw [AddMonoid.End.DualEndData.intLinComb_disc, AddMonoid.End.DualEndData.ofCharPoly_trace,
    AddMonoid.End.DualEndData.ofCharPoly_norm]

end SatGates
