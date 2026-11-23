import Def.Matrix_Main
import Theorem.ZMod.Gamma0UnitsChar
import Def.Matrix_IharaAmalgamMap
import Mathlib.Data.ZMod.Basic

namespace Ihara

open Matrix

open scoped MatrixGroups

variable (N q : ℕ)

noncomputable def zAwayToZMod (hNq : Nat.Coprime N q) : ZAway q →+* ZMod N :=
  IsLocalization.Away.lift (S := ZAway q) (g := Int.castRingHom (ZMod N)) (q : ℤ)
    (by rw [eq_intCast]; exact isUnit_intCast_q N q hNq)

noncomputable def gamma0AwayMap (hNq : Nat.Coprime N q) : Gamma0Away N q →* ZMod N where
  toFun g := zAwayToZMod N q hNq ((g : SL(2, ZAway q)) 1 1)
  map_one' := by
    have h : ((1 : Gamma0Away N q) : SL(2, ZAway q)) 1 1 = 1 := rfl
    rw [h, map_one]
  map_mul' a b := by
    have h : ((a * b : Gamma0Away N q) : SL(2, ZAway q)) 1 1
        = (a : SL(2, ZAway q)) 1 0 * (b : SL(2, ZAway q)) 0 1
          + (a : SL(2, ZAway q)) 1 1 * (b : SL(2, ZAway q)) 1 1 :=
      (Matrix.two_mul_expl (a : SL(2, ZAway q)).1 (b : SL(2, ZAway q)).1).2.2.2
    rw [h, map_add, map_mul, map_mul, zAwayToZMod_apply_one_zero N q hNq a, zero_mul,
      zero_add]

noncomputable def gamma0AwayUnitsChar (hNq : Nat.Coprime N q) :
    Gamma0Away N q →* (ZMod N)ˣ :=
  (gamma0AwayMap N q hNq).toHomUnits

noncomputable def vertexZeroAway : CongruenceSubgroup.Gamma0 N →* Gamma0Away N q :=
  (vertexZero N q).codRestrict (Gamma0Away N q) (vertexZero_mem N q)

noncomputable def vertexOneAway : CongruenceSubgroup.Gamma0 N →* Gamma0Away N q :=
  (vertexOne N q).codRestrict (Gamma0Away N q) (vertexOne_mem N q)

end Ihara
