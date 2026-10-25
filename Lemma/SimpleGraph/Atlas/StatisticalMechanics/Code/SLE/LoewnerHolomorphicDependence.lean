import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.SLE.LoewnerHolomorphicDependence.Part3
open Complex Set Metric Filter Topology StatMech StatMech.SLE


/--
[linearODE_terminal_eq_initial_mul_exp_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean)
-/
@[path]
private lemma linearODE_terminal_eq_initial_mul_exp_integral_eq
  {T : Real}
  {a f : Real -> Complex}
-- given
  (hT : 0 <= T)
  (ha : ContinuousOn a (Icc (0 : Real) T))
  (hf : ContinuousOn f (Icc (0 : Real) T))
  (hderiv : ∀ t ∈ Icc (0 : Real) T, HasDerivWithinAt f (a t * f t) (Icc (0 : Real) T) t) :
-- imply
  f T = f 0 * Complex.exp (∫ s in (0 : Real)..T, a s) := by
-- proof
  apply StatMech.SLE.linearODE_terminal_eq_initial_mul_exp_integral hT ha hf hderiv

/--
[loewnerField_hasDerivAt_initial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean)
-/
@[path]
private lemma loewnerField_hasDerivAt_initial_eq
  {t : Real}
  {z : Complex}
-- given
  (W : Real -> Real)
  (hz : z ≠ (W t : Complex)) :
-- imply
  HasDerivAt (loewnerField W t) (-2 / (z - (W t : Complex)) ^ 2) z := by
-- proof
  apply StatMech.SLE.loewnerField_hasDerivAt_initial W t hz

/--
[loewnerInitialJacobian_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean)
-/
@[path]
private lemma loewnerInitialJacobian_ne_zero_eq
  {t : Real}
  {z : Complex}
-- given
  (W : Real -> Real) :
-- imply
  loewnerInitialJacobian W t z ≠ 0 := by
-- proof
  apply StatMech.SLE.loewnerInitialJacobian_ne_zero W t z

/--
[loewnerInitialJacobian_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean)
-/
@[path]
private lemma loewnerInitialJacobian_zero_eq
  {z : Complex}
-- given
  (W : Real -> Real) :
-- imply
  loewnerInitialJacobian W 0 z = 1 := by
-- proof
  apply StatMech.SLE.loewnerInitialJacobian_zero W z

/--
[loewnerMaximalMaps_hasDerivAt_of_lt_im_sq_div_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean)
-/
@[path]
private lemma loewnerMaximalMaps_hasDerivAt_of_lt_im_sq_div_sixteen_eq
  {W : Real -> Real}
  {u : Real}
  {z : Complex}
-- given
  (hW : Continuous W)
  (hu : 0 <= u)
  (hz : z ∈ upperHalfPlane)
  (hshort : u < z.im ^ 2 / 16) :
-- imply
  HasDerivAt (loewnerMaximalMaps W u) (loewnerInitialJacobian W u z) z := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_hasDerivAt_of_lt_im_sq_div_sixteen hW hu hz hshort

/--
[loewnerMaximalMaps_hasDerivAt_initial_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean)
-/
@[path]
private lemma loewnerMaximalMaps_hasDerivAt_initial_zero_eq
  {W : Real -> Real}
  {z : Complex}
-- given
  (hW : Continuous W)
  (hz : z ∈ upperHalfPlane) :
-- imply
  HasDerivAt (loewnerMaximalMaps W 0) 1 z := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_hasDerivAt_initial_zero hW hz

/--
[hasLoewnerLocalInitialVariationalFormula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean)
-/
@[path]
private lemma hasLoewnerLocalInitialVariationalFormula_eq
  {W : Real -> Real}
-- given
  (hW : Continuous W) :
-- imply
  HasLoewnerLocalInitialVariationalFormula W := by
-- proof
  apply StatMech.SLE.hasLoewnerLocalInitialVariationalFormula hW

/--
[exists_loewnerMaximalMaps_hasDerivAt_ne_zero_of_localVariational](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean)
-/
@[path]
private lemma exists_loewnerMaximalMaps_hasDerivAt_ne_zero_of_localVariational_eq
  {W : Real -> Real}
  {t : Real}
  {z : Complex}
-- given
  (hW : Continuous W)
  (hlocal : HasLoewnerLocalInitialVariationalFormula W)
  (ht : 0 <= t)
  (hz : z ∈ loewnerUnswallowedDomain W t) :
-- imply
  exists c : Complex, c ≠ 0 /\ HasDerivAt (loewnerMaximalMaps W t) c z := by
-- proof
  apply StatMech.SLE.exists_loewnerMaximalMaps_hasDerivAt_ne_zero_of_localVariational hW hlocal ht hz

/--
[loewnerMaximalMaps_differentiableOn_of_localVariational](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean)
-/
@[path]
private lemma loewnerMaximalMaps_differentiableOn_of_localVariational_eq
  {W : Real -> Real}
  {t : Real}
-- given
  (hW : Continuous W)
  (hlocal : HasLoewnerLocalInitialVariationalFormula W)
  (ht : 0 <= t) :
-- imply
  DifferentiableOn Complex (loewnerMaximalMaps W t) (loewnerUnswallowedDomain W t) := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_differentiableOn_of_localVariational hW hlocal ht

/--
[loewnerMaximalMaps_conformalAt_of_localVariational](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean)
-/
@[path]
private lemma loewnerMaximalMaps_conformalAt_of_localVariational_eq
  {W : Real -> Real}
  {t : Real}
  {z : Complex}
-- given
  (hW : Continuous W)
  (hlocal : HasLoewnerLocalInitialVariationalFormula W)
  (ht : 0 <= t)
  (hz : z ∈ loewnerUnswallowedDomain W t) :
-- imply
  ConformalAt (loewnerMaximalMaps W t) z := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_conformalAt_of_localVariational hW hlocal ht hz

/--
[loewnerMaximalMaps_conformalOn_of_localVariational](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean)
-/
@[path]
private lemma loewnerMaximalMaps_conformalOn_of_localVariational_eq
  {W : Real -> Real}
  {t : Real}
-- given
  (hW : Continuous W)
  (hlocal : HasLoewnerLocalInitialVariationalFormula W)
  (ht : 0 <= t) :
-- imply
  forall z, z ∈ loewnerUnswallowedDomain W t -> ConformalAt (loewnerMaximalMaps W t) z := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_conformalOn_of_localVariational hW hlocal ht

/--
[exists_loewnerMaximalMaps_hasDerivAt_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean)
-/
@[path]
private lemma exists_loewnerMaximalMaps_hasDerivAt_ne_zero_eq
  {W : Real -> Real}
  {t : Real}
  {z : Complex}
-- given
  (hW : Continuous W)
  (ht : 0 <= t)
  (hz : z ∈ loewnerUnswallowedDomain W t) :
-- imply
  exists c : Complex, c ≠ 0 /\ HasDerivAt (loewnerMaximalMaps W t) c z := by
-- proof
  apply StatMech.SLE.exists_loewnerMaximalMaps_hasDerivAt_ne_zero hW ht hz

/--
[loewnerMaximalMaps_differentiableOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean)
-/
@[path]
private lemma loewnerMaximalMaps_differentiableOn_eq
  {W : Real -> Real}
  {t : Real}
-- given
  (hW : Continuous W)
  (ht : 0 <= t) :
-- imply
  DifferentiableOn Complex (loewnerMaximalMaps W t) (loewnerUnswallowedDomain W t) := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_differentiableOn hW ht

/--
[loewnerMaximalMaps_conformalAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean)
-/
@[path]
private lemma loewnerMaximalMaps_conformalAt_eq
  {W : Real -> Real}
  {t : Real}
  {z : Complex}
-- given
  (hW : Continuous W)
  (ht : 0 <= t)
  (hz : z ∈ loewnerUnswallowedDomain W t) :
-- imply
  ConformalAt (loewnerMaximalMaps W t) z := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_conformalAt hW ht hz

/--
[loewnerMaximalMaps_conformalOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean)
-/
@[path]
private lemma loewnerMaximalMaps_conformalOn_eq
  {W : Real -> Real}
  {t : Real}
-- given
  (hW : Continuous W)
  (ht : 0 <= t) :
-- imply
  forall z, z ∈ loewnerUnswallowedDomain W t -> ConformalAt (loewnerMaximalMaps W t) z := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_conformalOn hW ht


-- created on 2026-10-23
