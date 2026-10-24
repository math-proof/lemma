import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFourier
open StatMech StatMech.FrontierA


/--
[one_sub_triangularTorusKWMatrix_eq_blockCirculant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFourier.lean)
-/
@[path]
private lemma one_sub_triangularTorusKWMatrix_eq_blockCirculant_eq
  {L : Nat}
  {t1 t2 t3 rho u v : Complex} :
-- imply
  1 - triangularTorusKWMatrix L t1 t2 t3 rho u v = ons_blockCirculant2D L 6 (fun g => (if g = 0 then (1 : Matrix (Fin 6) (Fin 6) Complex) else 0) - triangularTorusKWBlock L t1 t2 t3 rho u v g) := by
-- proof
  apply StatMech.FrontierA.one_sub_triangularTorusKWMatrix_eq_blockCirculant L t1 t2 t3 rho u v

/--
[triangularTorusKWBlock_symbol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFourier.lean)
-/
@[path]
private lemma triangularTorusKWBlock_symbol_eq
  {L : Nat}
  [NeZero L]
  {t1 t2 t3 rho u v root : Complex}
  {j : ZMod L × ZMod L}
-- given
  (hroot : IsPrimitiveRoot root L)
  (hu : u ≠ 0)
  (hv : v ≠ 0) :
-- imply
  ons_blockSymbol2D L 6 root (fun g => (if g = 0 then (1 : Matrix (Fin 6) (Fin 6) Complex) else 0) - triangularTorusKWBlock L t1 t2 t3 rho u v g) j = triangularKacWardSymbolMatrix t1 t2 t3 rho (u * root ^ j.1.val) (v * root ^ j.2.val) ((u * root ^ j.1.val) * (v * root ^ j.2.val)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusKWBlock_symbol L t1 t2 t3 rho u v root hroot hu hv j

/--
[triangularTorusKWMatrix_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFourier.lean)
-/
@[path]
private lemma triangularTorusKWMatrix_det_eq
  {L : Nat}
  [NeZero L]
  {t1 t2 t3 rho u v root : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hroot : IsPrimitiveRoot root L)
  (hu : u ≠ 0)
  (hv : v ≠ 0) :
-- imply
  (1 - triangularTorusKWMatrix L t1 t2 t3 rho u v).det = ∏ j : ZMod L × ZMod L, ((1 + t1 ^ 2) * (1 + t2 ^ 2) * (1 + t3 ^ 2) + 8 * t1 * t2 * t3 - t1 * (1 - t2 ^ 2) * (1 - t3 ^ 2) * (u * root ^ j.1.val + (u * root ^ j.1.val) ⁻¹) - t2 * (1 - t1 ^ 2) * (1 - t3 ^ 2) * (v * root ^ j.2.val + (v * root ^ j.2.val) ⁻¹) - t3 * (1 - t1 ^ 2) * (1 - t2 ^ 2) * ((u * root ^ j.1.val) * (v * root ^ j.2.val) + ((u * root ^ j.1.val) * (v * root ^ j.2.val)) ⁻¹)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusKWMatrix_det L t1 t2 t3 rho u v root hrho hroot hu hv


-- created on 2026-10-23
