module

public import Theorem.Matrix.Main
public import Theorem.ZMod.Gamma0UnitsChar
public import Theorem.Matrix.IharaAmalgamMap
public import Mathlib.Data.ZMod.Basic

public section

namespace Ihara

open Matrix

open scoped MatrixGroups

variable (N q : ℕ)

public theorem isUnit_intCast_q (hNq : Nat.Coprime N q) : IsUnit (((q : ℤ) : ZMod N)) := by
  have h : ((ZMod.unitOfCoprime q hNq.symm : (ZMod N)ˣ) : ZMod N) = (((q : ℤ)) : ZMod N) := by
    rw [ZMod.coe_unitOfCoprime, Int.cast_natCast]
  exact h ▸ (ZMod.unitOfCoprime q hNq.symm).isUnit


@[simp]
public theorem zAwayToZMod_algebraMap (hNq : Nat.Coprime N q) (a : ℤ) :
    zAwayToZMod N q hNq (algebraMap ℤ (ZAway q) a) = (a : ZMod N) := by
  rw [zAwayToZMod, IsLocalization.Away.lift_eq, eq_intCast]


public theorem zAwayToZMod_natCast_self (hNq : Nat.Coprime N q) :
    zAwayToZMod N q hNq (N : ZAway q) = 0 := by
  have h : ((N : ℕ) : ZAway q) = algebraMap ℤ (ZAway q) ((N : ℕ) : ℤ) := by simp
  rw [h, zAwayToZMod_algebraMap, Int.cast_natCast, ZMod.natCast_self]


public theorem zAwayToZMod_apply_one_zero (hNq : Nat.Coprime N q) (g : Gamma0Away N q) :
    zAwayToZMod N q hNq ((g : SL(2, ZAway q)) 1 0) = 0 := by
  obtain ⟨r, hr⟩ := g.2
  rw [hr, map_mul, zAwayToZMod_natCast_self, zero_mul]


@[simp]
public theorem gamma0AwayUnitsChar_coe (hNq : Nat.Coprime N q) (g : Gamma0Away N q) :
    (gamma0AwayUnitsChar N q hNq g : ZMod N) = gamma0AwayMap N q hNq g :=
  rfl


public theorem gamma0AwayUnitsChar_comp_vertexZeroAway (hNq : Nat.Coprime N q) :
    (gamma0AwayUnitsChar N q hNq).comp (vertexZeroAway N q) = gamma0UnitsHom N := by
  ext g
  show zAwayToZMod N q hNq ((vertexZero N q g : SL(2, ZAway q)) 1 1)
      = CongruenceSubgroup.Gamma0Map N g
  have h : (vertexZero N q g : SL(2, ZAway q)) 1 1
      = algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 1) := rfl
  rw [h, zAwayToZMod_algebraMap]
  rfl


public theorem gamma0AwayUnitsChar_comp_vertexOneAway (hNq : Nat.Coprime N q) :
    (gamma0AwayUnitsChar N q hNq).comp (vertexOneAway N q) = gamma0UnitsHom N := by
  ext g
  show zAwayToZMod N q hNq ((vertexOne N q g : SL(2, ZAway q)) 1 1)
      = CongruenceSubgroup.Gamma0Map N g
  have h : (vertexOne N q g : SL(2, ZAway q)) 1 1
      = algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 1) := by
    rw [coe_vertexOne_eq]
    rfl
  rw [h, zAwayToZMod_algebraMap]
  rfl

end Ihara
