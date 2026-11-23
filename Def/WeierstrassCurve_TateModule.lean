import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Def.GaloisRep_Adic
import Def.WeierstrassCurve_Basic
import Theorem.WeierstrassCurve.GaloisRep
import Instance.EllipticCurve_TateModule

open IsLocalRing

namespace TateModule

variable {p : ℕ} {M : Type} [AddCommGroup M]

variable [Fact p.Prime]

variable (p M) in

def proj (n : ℕ) : TateModule p M →+ M where
  toFun x := (x : ℕ → M) n
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Fact p.Prime] in
def shiftOfProjEqZero (n : ℕ) (x : TateModule p M) (hx : proj p M n x = 0) : TateModule p M :=
  ⟨fun m => (x : ℕ → M) (m + n), fun m =>
    ⟨by
      show ((p ^ m : ℕ) : ℤ) • (x : ℕ → M) (m + n) = 0
      rw [Nat.add_comm, compat_pow x n m]; exact hx,
     by
      show ((p : ℕ) : ℤ) • (x : ℕ → M) (m + 1 + n) = (x : ℕ → M) (m + n)
      rw [Nat.add_right_comm]; exact compat x (m + n)⟩⟩

section action

variable {G : Type} [Monoid G] [DistribMulAction G M]

variable (p M G) in

noncomputable def rep : G →* Module.End ℤ_[p] (TateModule p M) where
  toFun g :=
    { toFun := fun x => ⟨fun n => g • (x : ℕ → M) n, fun n =>
        ⟨by
          show ((p ^ n : ℕ) : ℤ) • DistribSMul.toAddMonoidHom M g ((x : ℕ → M) n) = 0
          rw [← map_zsmul, torsion, map_zero],
         by
          show ((p : ℕ) : ℤ) • DistribSMul.toAddMonoidHom M g ((x : ℕ → M) (n + 1)) = _
          rw [← map_zsmul, compat]; rfl⟩⟩
      map_add' := fun x y => Subtype.ext (funext fun n => by
        show g • ((x + y : TateModule p M) : ℕ → M) n = g • (x : ℕ → M) n + g • (y : ℕ → M) n
        rw [coe_add, Pi.add_apply, smul_add])
      map_smul' := fun a x => Subtype.ext (funext fun n => by
        show g • (((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n) = ((a.appr n : ℕ) : ℤ) • (g • (x : ℕ → M) n)
        exact map_zsmul (DistribSMul.toAddMonoidHom M g) _ _) }
  map_one' := LinearMap.ext fun x => Subtype.ext (funext fun n => one_smul G ((x : ℕ → M) n))
  map_mul' g h := LinearMap.ext fun x => Subtype.ext (funext fun n => mul_smul g h ((x : ℕ → M) n))

end action


end TateModule

namespace FreyPackageGaloisRep

variable (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
noncomputable def padicIntToRingLevel (hp : (p : 𝒪) ∈ maximalIdeal 𝒪) (n : ℕ) :
    ℤ_[p] →+* 𝒪 ⧸ maximalIdeal 𝒪 ^ n :=
  (ZMod.castHom (ringChar_quotient_dvd 𝒪 p hp n) (𝒪 ⧸ maximalIdeal 𝒪 ^ n)).comp (PadicInt.toZModPow n)

variable [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

noncomputable def padicIntToRing (hp : (p : 𝒪) ∈ maximalIdeal 𝒪) : ℤ_[p] →+* 𝒪 :=
  IsAdicComplete.liftRingHom (maximalIdeal 𝒪) (padicIntToRingLevel 𝒪 p hp)
    (fun hle => padicIntToRingLevel_compat 𝒪 p hp hle)

end FreyPackageGaloisRep

namespace TateModule

open Submodule

variable {p : ℕ} {M : Type} [AddCommGroup M]

section Counting

variable [Fact p.Prime]

variable (p M) in

def mulP (n : ℕ) : torsionBy ℤ M ((p ^ (n + 1) : ℕ) : ℤ) →+ torsionBy ℤ M ((p ^ n : ℕ) : ℤ) where
  toFun m := ⟨((p : ℕ) : ℤ) • (m : M), smul_mem_torsionBy_of_mem_succ m.2⟩
  map_zero' := Subtype.ext (smul_zero _)
  map_add' _ _ := Subtype.ext (smul_add _ _ _)

omit [Fact p.Prime] in
variable (p M) in

def kerMulPEquiv (n : ℕ) : (mulP p M n).ker ≃ torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ) where
  toFun m := ⟨(m.1 : M), mem_torsionBy_one_of_smul_eq_zero (by
    have h := m.2; rw [AddMonoidHom.mem_ker] at h; exact congrArg Subtype.val h)⟩
  invFun m := ⟨⟨(m : M), by
      rw [mem_torsionBy_iff, pow_succ, Nat.cast_mul, mul_smul, smul_eq_zero_of_mem_torsionBy_one m.2,
        smul_zero]⟩,
    by rw [AddMonoidHom.mem_ker]; exact Subtype.ext (smul_eq_zero_of_mem_torsionBy_one m.2)⟩
  left_inv m := rfl
  right_inv m := rfl

noncomputable def liftAux
    (next : (k : ℕ) → torsionBy ℤ M ((p ^ k : ℕ) : ℤ) → torsionBy ℤ M ((p ^ (k + 1) : ℕ) : ℤ))
    (n : ℕ) (m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) : (j : ℕ) → torsionBy ℤ M ((p ^ (n + j) : ℕ) : ℤ)
  | 0 => m
  | j + 1 => next (n + j) (liftAux next n m j)

noncomputable def liftFun
    (next : (k : ℕ) → torsionBy ℤ M ((p ^ k : ℕ) : ℤ) → torsionBy ℤ M ((p ^ (k + 1) : ℕ) : ℤ))
    (n : ℕ) (m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) (k : ℕ) : M :=
  if n ≤ k then (liftAux next n m (k - n) : M) else ((p ^ (n - k) : ℕ) : ℤ) • (m : M)

omit [Fact p.Prime] in
end Counting

section Free

variable [Fact p.Prime]

noncomputable def levelMap (x y : TateModule p M) (n : ℕ) (c : ZMod (p ^ n) × ZMod (p ^ n)) :
    torsionBy ℤ M ((p ^ n : ℕ) : ℤ) :=
  ⟨(c.1.val : ℤ) • (x : ℕ → M) n + (c.2.val : ℤ) • (y : ℕ → M) n, by
    rw [mem_torsionBy_iff, smul_add, smul_comm _ (c.1.val : ℤ), torsion, smul_comm _ (c.2.val : ℤ), torsion,
      smul_zero, smul_zero, add_zero]⟩

noncomputable def basisOfCard (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2) :
    Module.Basis (Fin 2) ℤ_[p] (TateModule p M) :=
  Module.Basis.mk (v := ![(exists_pair hcard).choose, (exists_pair hcard).choose_spec.choose])
    (linearIndependent_pair (exists_pair hcard).choose_spec.choose_spec)
    (top_le_span_pair hcard (exists_pair hcard).choose_spec.choose_spec)

end Free

end TateModule


namespace WeierstrassCurve

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

def Affine.Point.coords {F : Type} [Field F] {W : WeierstrassCurve F} : W.toAffine.Point → Set F
  | 0 => ∅
  | @Affine.Point.some _ _ _ x y _ => {x, y}

variable (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]

noncomputable def torsionField (n : ℕ) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ
    (⋃ P ∈ (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ) :
        Set (W⁄(AlgebraicClosure ℚ)).Point),
      Affine.Point.coords (W := W.baseChange (AlgebraicClosure ℚ)) P)

omit [Fact p.Prime] in
noncomputable def tateModuleRepOfBasis
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ))
      = (p ^ n) ^ 2)
    (b : Module.Basis (Fin 2) ℤ_[p] (TateModule p (W⁄(AlgebraicClosure ℚ)).Point)) :
    GaloisRepAdic ℤ_[p] where
  V := TateModule p (W⁄(AlgebraicClosure ℚ)).Point
  instFree := Module.Free.of_basis b
  instFinite := Module.Finite.of_basis b
  finrank_eq := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  ρ := TateModule.rep p (W⁄(AlgebraicClosure ℚ)).Point (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  isAdicContinuous := W.tateModule_isAdicContinuous p
    fun n => W.finite_torsionBy_of_card p n (hcard n) (Nat.Prime.ne_zero Fact.out)

end WeierstrassCurve


namespace WeierstrassCurve

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

noncomputable def tateModuleRep (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hcard : ∀ n : ℕ,
      Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2) :
    GaloisRepAdic ℤ_[p] :=
  W.tateModuleRepOfBasis p hcard (TateModule.basisOfCard hcard)

end WeierstrassCurve
