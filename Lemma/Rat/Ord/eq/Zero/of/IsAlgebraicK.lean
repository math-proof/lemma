import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open Polynomial
open AlgebraicCurve.Place AlgebraicCurve
open Int


/--
[AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic.lean)
-/

private lemma mem_of_isAlgebraic
  [Field K]
  [Field F]
  [Algebra K F]
  (v : AlgebraicCurve.Place K F)
  {x : F} (hx : IsAlgebraic K x) : x ∈ v.toValuationSubring := by
  have hint : IsIntegral K x := hx.isIntegral
  refine v.mem_of_eval_monic_eq_zero (P := (minpoly K x).map (algebraMap K F)) ((minpoly.monic hint).map _)
    (fun i => ?_) ?_
  ·
    rw [coeff_map]
    exact v.algebraMap_mem' _
  · rw [eval_map_algebraMap, minpoly.aeval]

private lemma  ord_eq_zero_of_isAlgebraic'
  [Field K]
  [Field F]
  [Algebra K F]
  (v : AlgebraicCurve.Place K F)
  {x : F} (hx : IsAlgebraic K x) : v.ord x = 0 := by
  if hx0 : x = 0 then
    simp [hx0, v.ord_zero]
  else
    let u : v.toValuationSubringˣ :=
      { val := ⟨x, mem_of_isAlgebraic v hx⟩
        inv := ⟨x⁻¹, mem_of_isAlgebraic v hx.inv⟩
        val_inv := Subtype.ext (mul_inv_cancel₀ hx0)
        inv_val := Subtype.ext (inv_mul_cancel₀ hx0) }
    exact v.ord_coe_unit u
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {v : AlgebraicCurve.Place K F}
  {x : F}
-- given
  (hx : IsAlgebraic K x) :
-- imply
  v.ord x = 0 :=
-- proof
  ord_eq_zero_of_isAlgebraic' v hx


-- created on 2026-10-24
