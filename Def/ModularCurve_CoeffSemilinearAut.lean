module

public import Theorem.HahnSeries.JqCoeff
public import Theorem.LaurentSeries.LaurentCoeff
public import Theorem.Scheme.AlgebraicCurveBaseChangeGalois
public import Mathlib.FieldTheory.Perfect

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IntermediateField HahnSeries

namespace ModularCurve


section CoeffAut

variable {K : Type*} [Field K] (N : ℕ) [NeZero N]

def coeffRingAut (τ : K ≃+* K) : modularFunctionFieldC K N ≃+* modularFunctionFieldC K N where
  toFun x := ⟨coeffMap (τ : K →+* K) (x : LaurentSeries K),
    coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC N (τ : K →+* K) x.2⟩
  invFun x := ⟨coeffMap (τ.symm : K →+* K) (x : LaurentSeries K),
    coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC N (τ.symm : K →+* K) x.2⟩
  left_inv x := Subtype.ext <| by
    show coeffMap (τ.symm : K →+* K) (coeffMap (τ : K →+* K) (x : LaurentSeries K))
      = (x : LaurentSeries K)
    rw [coeffMap_coeffMap,
      coeffMap_congr (g := RingHom.id K) (RingHom.ext fun a => τ.symm_apply_apply a) _, coeffMap_id]
  right_inv x := Subtype.ext <| by
    show coeffMap (τ : K →+* K) (coeffMap (τ.symm : K →+* K) (x : LaurentSeries K))
      = (x : LaurentSeries K)
    rw [coeffMap_coeffMap,
      coeffMap_congr (g := RingHom.id K) (RingHom.ext fun a => τ.apply_symm_apply a) _, coeffMap_id]
  map_mul' x y :=
    Subtype.ext (map_mul (coeffMap (τ : K →+* K)) (x : LaurentSeries K) (y : LaurentSeries K))
  map_add' x y :=
    Subtype.ext (map_add (coeffMap (τ : K →+* K)) (x : LaurentSeries K) (y : LaurentSeries K))

def coeffSemilinearAut (τ : K ≃+* K) : SemilinearAut K (modularFunctionFieldC K N) :=
  ⟨(coeffRingAut N τ, τ), fun a => coeffRingAut_algebraMap N τ a⟩

end CoeffAut

section Frobenius

variable (q : ℕ) (K : Type*) [Field K] [Fact q.Prime] [CharP K q] [PerfectField K]
  (N : ℕ) [NeZero N]

def arithFrobC : SemilinearAut K (modularFunctionFieldC K N) :=
  coeffSemilinearAut N (frobeniusEquiv K q)

end Frobenius

end ModularCurve

end

end
