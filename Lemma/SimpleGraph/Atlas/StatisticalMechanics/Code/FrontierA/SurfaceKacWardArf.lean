import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part5
open StatMech StatMech.FrontierA


/--
[surfaceParitySign_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean)
-/
@[path]
private lemma surfaceParitySign_zero_eq :
-- imply
  surfaceParitySign 0 = 1 := by
-- proof
  apply StatMech.FrontierA.surfaceParitySign_zero

/--
[surfaceParitySign_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean)
-/
@[path]
private lemma surfaceParitySign_add_eq
  {z w : Fin 2} :
-- imply
  surfaceParitySign (z + w) = surfaceParitySign z * surfaceParitySign w := by
-- proof
  apply StatMech.FrontierA.surfaceParitySign_add z w

/--
[surfaceParitySign_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean)
-/
@[path]
private lemma surfaceParitySign_finset_sum_eq
  [DecidableEq ι]
  {S : Finset ι}
  {f : ι → Fin 2} :
-- imply
  surfaceParitySign (∑ i ∈ S, f i) = ∏ i ∈ S, surfaceParitySign (f i) := by
-- proof
  apply StatMech.FrontierA.surfaceParitySign_finset_sum S f

/--
[surfaceParitySign_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean)
-/
@[path]
private lemma surfaceParitySign_sum_eq
  {g : Nat}
  {f : Fin g → Fin 2} :
-- imply
  surfaceParitySign (∑ i, f i) = ∏ i, surfaceParitySign (f i) := by
-- proof
  apply StatMech.FrontierA.surfaceParitySign_sum f

/--
[surfaceQuadraticParity_local_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean)
-/
@[path]
private lemma surfaceQuadraticParity_local_add_eq
  {a b x y x' y' : Fin 2} :
-- imply
  (x + x') * (y + y') + a * (x + x') + b * (y + y') = (x * y + a * x + b * y) + (x' * y' + a * x' + b * y') + (x * y' + y * x') := by
-- proof
  apply StatMech.FrontierA.surfaceQuadraticParity_local_add a b x y x' y'

/--
[surfaceQuadraticParity_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean)
-/
@[path]
private lemma surfaceQuadraticParity_add_eq
  {g : Nat}
  {lambda : SurfaceSpinStructure g}
-- given
  (h k : SurfaceHomology g) :
-- imply
  surfaceQuadraticParity lambda (h + k) = surfaceQuadraticParity lambda h + surfaceQuadraticParity lambda k + surfaceIntersection h k := by
-- proof
  apply StatMech.FrontierA.surfaceQuadraticParity_add lambda h k

/--
[surfaceLocalArfQuadratic_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean)
-/
@[path]
private lemma surfaceLocalArfQuadratic_sum_eq
  {x y : Fin 2} :
-- imply
  (∑ ab : Fin 2 × Fin 2, surfaceParitySign (surfaceLocalArfQuadraticExponent x y ab.1 ab.2)) = 2 := by
-- proof
  apply StatMech.FrontierA.surfaceLocalArfQuadratic_sum x y

/--
[surfaceArf_add_quadratic_eq_sum_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean)
-/
@[path]
private lemma surfaceArf_add_quadratic_eq_sum_local_eq
  {g : Nat}
  {lambda : SurfaceSpinStructure g}
-- given
  (h : SurfaceHomology g) :
-- imply
  surfaceArfParity lambda + surfaceQuadraticParity lambda h = ∑ i, surfaceLocalArfQuadraticExponent (h.1 i) (h.2 i) (lambda.1 i) (lambda.2 i) := by
-- proof
  apply StatMech.FrontierA.surfaceArf_add_quadratic_eq_sum_local lambda h

/--
[surfaceSpinFunctionEquiv_apply_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean)
-/
@[path]
private lemma surfaceSpinFunctionEquiv_apply_fst_eq
  {g : Nat}
  {lambda : SurfaceSpinStructure g}
  {i : Fin g} :
-- imply
  (surfaceSpinFunctionEquiv g lambda i).1 = lambda.1 i := by
-- proof
  apply StatMech.FrontierA.surfaceSpinFunctionEquiv_apply_fst g lambda i

/--
[surfaceSpinFunctionEquiv_apply_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean)
-/
@[path]
private lemma surfaceSpinFunctionEquiv_apply_snd_eq
  {g : Nat}
  {lambda : SurfaceSpinStructure g}
  {i : Fin g} :
-- imply
  (surfaceSpinFunctionEquiv g lambda i).2 = lambda.2 i := by
-- proof
  apply StatMech.FrontierA.surfaceSpinFunctionEquiv_apply_snd g lambda i

/--
[surface_arf_character_orthogonality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean)
-/
@[path]
private lemma surface_arf_character_orthogonality_eq
  {g : Nat}
-- given
  (h : SurfaceHomology g) :
-- imply
  (∑ lambda : SurfaceSpinStructure g, surfaceParitySign (surfaceArfParity lambda + surfaceQuadraticParity lambda h)) = (2 : Real) ^ g := by
-- proof
  apply StatMech.FrontierA.surface_arf_character_orthogonality g h

/--
[surface_arf_reconstruction_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean)
-/
@[path]
private lemma surface_arf_reconstruction_mul_eq
  {g : Nat}
  {weight : SurfaceHomology g → Real} :
-- imply
  (2 : Real) ^ g * surfaceUnsignedSectorSum weight = ∑ lambda : SurfaceSpinStructure g, surfaceParitySign (surfaceArfParity lambda) * surfaceTwistedSectorRoot weight lambda := by
-- proof
  apply StatMech.FrontierA.surface_arf_reconstruction_mul g weight

/--
[surface_arf_reconstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean)
-/
@[path]
private lemma surface_arf_reconstruction_eq
  {g : Nat}
  {weight : SurfaceHomology g → Real} :
-- imply
  surfaceUnsignedSectorSum weight = ((2 : Real) ^ g)⁻¹ * ∑ lambda : SurfaceSpinStructure g, surfaceParitySign (surfaceArfParity lambda) * surfaceTwistedSectorRoot weight lambda := by
-- proof
  apply StatMech.FrontierA.surface_arf_reconstruction g weight

/--
[surfaceTwistedSectorSquare_eq_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean)
-/
@[path]
private lemma surfaceTwistedSectorSquare_eq_sq_eq
  {g : Nat}
  {weight : SurfaceHomology g → Real}
  {lambda : SurfaceSpinStructure g} :
-- imply
  surfaceTwistedSectorSquare weight lambda = surfaceTwistedSectorRoot weight lambda ^ 2 := by
-- proof
  apply StatMech.FrontierA.surfaceTwistedSectorSquare_eq_sq weight lambda


-- created on 2026-10-23
