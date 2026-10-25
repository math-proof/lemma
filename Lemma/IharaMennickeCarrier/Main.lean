import Lemma.Gamma0Away.Main
import Lemma.IharaAmalgamMap.Main
import Lemma.Gamma0AwayUnitsChar.Main
import Mathlib.GroupTheory.Subgroup.Simple
import Instance.IharaMennickeCarrier

open Matrix

open scoped MatrixGroups

namespace Ihara

section MennickeGenerator

def mennickeA : SL(2, ℤ) :=
  ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[simp]
theorem mennickeA_coe :
    ((mennickeA : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 1, 1] := rfl

theorem mennickeA_pow_coe (k : ℕ) :
    ((mennickeA ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; (k : ℤ), 1] := by
  induction k with
  | zero => simp [Matrix.one_fin_two]
  | succ k ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, mennickeA_coe, Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp

end MennickeGenerator

section Carrier

variable (N q : ℕ)

noncomputable def slAwayReduction (hNq : Nat.Coprime N q) : SL(2, ZAway q) →* SL(2, ZMod N) :=
  Matrix.SpecialLinearGroup.map (zAwayToZMod N q hNq)

theorem slAwayReduction_coe (hNq : Nat.Coprime N q) (g : SL(2, ZAway q)) :
    ((slAwayReduction N q hNq g : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      (g : Matrix (Fin 2) (Fin 2) (ZAway q)).map (zAwayToZMod N q hNq) := rfl

noncomputable def principalCongruenceAway (hNq : Nat.Coprime N q) :
    Subgroup SL(2, ZAway q) :=
  (slAwayReduction N q hNq).ker

theorem mem_principalCongruenceAway_iff (hNq : Nat.Coprime N q) {g : SL(2, ZAway q)} :
    g ∈ principalCongruenceAway N q hNq ↔ slAwayReduction N q hNq g = 1 := Iff.rfl

def MennickeCSP (hNq : Nat.Coprime N q) : Prop :=
  principalCongruenceAway N q hNq =
    Subgroup.normalClosure ({(slToAway q mennickeA) ^ N} : Set SL(2, ZAway q))

theorem slToAway_mennickeA_pow_mem (hNq : Nat.Coprime N q) :
    (slToAway q mennickeA) ^ N ∈ principalCongruenceAway N q hNq := by
  rw [mem_principalCongruenceAway_iff, ← map_pow]
  apply Subtype.ext
  rw [slAwayReduction_coe, coe_slToAway, mennickeA_pow_coe, Matrix.map_map,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, Function.comp_apply]

theorem normalClosure_le_principalCongruenceAway (hNq : Nat.Coprime N q) :
    Subgroup.normalClosure ({(slToAway q mennickeA) ^ N} : Set SL(2, ZAway q)) ≤
      principalCongruenceAway N q hNq :=
  Subgroup.normalClosure_le_normal
    (Set.singleton_subset_iff.mpr (slToAway_mennickeA_pow_mem N q hNq))

theorem mennickeCSP_iff_ker_le (hNq : Nat.Coprime N q) :
    MennickeCSP N q hNq ↔
      principalCongruenceAway N q hNq ≤
        Subgroup.normalClosure ({(slToAway q mennickeA) ^ N} : Set SL(2, ZAway q)) := by
  constructor
  · intro h; rw [h]
  · intro h; exact le_antisymm h (normalClosure_le_principalCongruenceAway N q hNq)

end Carrier

section DiagonalGenerator

noncomputable section

variable (q : ℕ)

def qInv : ZAway q := IsLocalization.Away.invSelf (S := ZAway q) ((q : ℕ) : ℤ)

theorem natCast_q_mul_qInv : ((q : ℕ) : ZAway q) * qInv q = 1 :=
  q_mul_invSelf q

theorem qInv_mul_natCast_q : qInv q * ((q : ℕ) : ZAway q) = 1 :=
  invSelf_mul_q q

def mennickeU : SL(2, ZAway q) :=
  ⟨!![((q : ℕ) : ZAway q), 0; 0, qInv q], by
    rw [Matrix.det_fin_two_of, natCast_q_mul_qInv q]; ring⟩

@[simp]
theorem mennickeU_coe :
    ((mennickeU q : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![((q : ℕ) : ZAway q), 0; 0, qInv q] := rfl

end

end DiagonalGenerator

open scoped MatrixGroups commutatorElement

section Carrier

variable (q m : ℕ)

noncomputable abbrev mennickeQ : Subgroup SL(2, ZAway q) :=
  Subgroup.normalClosure ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))

noncomputable def mennickeZ (hmq : Nat.Coprime m q) : Subgroup SL(2, ZAway q) :=
  Subgroup.comap
    (QuotientGroup.mk' (mennickeQ q m))
    (Subgroup.centralizer
      (Subgroup.map (QuotientGroup.mk' (mennickeQ q m))
        (principalCongruenceAway m q hmq)))

theorem mem_mennickeZ_iff (hmq : Nat.Coprime m q) (g : SL(2, ZAway q)) :
    g ∈ mennickeZ q m hmq ↔
      ∀ X ∈ principalCongruenceAway m q hmq, ⁅g, X⁆ ∈ mennickeQ q m := by
  constructor
  · intro hg X hX
    rw [mennickeZ, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hg
    have hcomm := hg (QuotientGroup.mk' _ X) (Subgroup.mem_map_of_mem _ hX)
    rw [← QuotientGroup.ker_mk' (mennickeQ q m), MonoidHom.mem_ker,
      map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.symm
  · intro h
    rw [mennickeZ, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_map] at hy
    obtain ⟨X, hX, rfl⟩ := hy
    have hc := h X hX
    rw [← QuotientGroup.ker_mk' (mennickeQ q m), MonoidHom.mem_ker,
      map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc.symm

theorem mennickeQ_le_mennickeZ (hmq : Nat.Coprime m q) :
    mennickeQ q m ≤ mennickeZ q m hmq := by
  intro x hx
  rw [mennickeZ, Subgroup.mem_comap]
  have hx1 : QuotientGroup.mk' (mennickeQ q m) x = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hx
  rw [hx1]
  exact Subgroup.one_mem _

end Carrier

section Regimes

variable (q m : ℕ)

def MennickeSaturated : Prop :=
  (q ^ 2 - 1) ∣ m ∧ ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1)

def MennickeCentralityCoprime (hmq : Nat.Coprime m q) : Prop :=
  Nat.Coprime m (q ^ 2 - 1) → mennickeZ q m hmq = ⊤

def MennickeLemma22Statement : Prop :=
  ∀ m : ℕ, ∀ hmq : Nat.Coprime m q, MennickeSaturated q m → mennickeZ q m hmq = ⊤

end Regimes

section Lemma21

variable (q m : ℕ) [NeZero q]

def MennickeLemma21 (hmq : Nat.Coprime m q) : Prop :=
  mennickeU q ∈ mennickeZ q m hmq

omit [NeZero q] in

theorem mennickeLemma21_iff (hmq : Nat.Coprime m q) :
    MennickeLemma21 q m hmq ↔ mennickeU q ∈ mennickeZ q m hmq :=
  Iff.rfl

end Lemma21

end Ihara
