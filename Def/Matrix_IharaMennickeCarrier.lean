module
public import Def.Matrix_Main
public import Def.Matrix_IharaAmalgamMap
public import Def.Matrix_Gamma0AwayUnitsChar
public import Mathlib.GroupTheory.Subgroup.Simple
public import Instance.IharaMennickeCarrier
open Matrix
open scoped MatrixGroups


public section

namespace Ihara

section MennickeGenerator

def mennickeA : SL(2, ℤ) :=
  ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; ring⟩

end MennickeGenerator

section Carrier

variable (N q : ℕ)

noncomputable def slAwayReduction (hNq : Nat.Coprime N q) : SL(2, ZAway q) →* SL(2, ZMod N) :=
  Matrix.SpecialLinearGroup.map (zAwayToZMod N q hNq)

noncomputable def principalCongruenceAway (hNq : Nat.Coprime N q) :
    Subgroup SL(2, ZAway q) :=
  (slAwayReduction N q hNq).ker

def MennickeCSP (hNq : Nat.Coprime N q) : Prop :=
  principalCongruenceAway N q hNq =
    Subgroup.normalClosure ({(slToAway q mennickeA) ^ N} : Set SL(2, ZAway q))

end Carrier

section DiagonalGenerator

noncomputable section

variable (q : ℕ)

def qInv : ZAway q := IsLocalization.Away.invSelf (S := ZAway q) ((q : ℕ) : ℤ)

def mennickeU : SL(2, ZAway q) :=
  ⟨!![((q : ℕ) : ZAway q), 0; 0, qInv q], by
    rw [Matrix.det_fin_two_of, natCast_q_mul_qInv q]; ring⟩

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

end Lemma21

end Ihara
