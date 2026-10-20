import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.FractionalIdeal.GroupAction
open scoped nonZeroDivisors
open scoped Pointwise
open scoped FractionalIdealUnits
open FractionalIdeal


/--
[units_smul_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/GroupAction.lean)
-/
@[path]
private lemma units_smul_val_eq
  [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] [IsFractionRing R K] [Group G] [MulSemiringAction G R]
  {g : G}
  {I : (FractionalIdeal R⁰ K)ˣ} :
-- imply
  ((g • I : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) =
    g • (I : FractionalIdeal R⁰ K) := by
-- proof
  apply FractionalIdeal.units_smul_val R K g I

/--
[smul_def](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/GroupAction.lean)
-/
@[path]
private lemma smul_def_eq
  [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] [IsFractionRing R K] [Group G] [MulSemiringAction G R]
  {g : G}
  {I : FractionalIdeal R⁰ K} :
-- imply
  g • I =
    FractionalIdeal.ringEquivOfRingEquiv K K
    (MulSemiringAction.toRingAut G R g) I := by
-- proof
  apply FractionalIdeal.smul_def R K g I

/--
[mem_smul_iff_exists](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/GroupAction.lean)
-/
@[path]
private lemma mem_smul_iff_exists_eq
  [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] [IsFractionRing R K] [Group G] [MulSemiringAction G R]
  {g : G}
  {I : FractionalIdeal R⁰ K}
  {x : K} :
-- imply
  x ∈ g • I ↔ ∃ y ∈ I,
    IsFractionRing.ringEquivOfRingEquiv
    (MulSemiringAction.toRingAut G R g) y = x := by
-- proof
  apply FractionalIdeal.mem_smul_iff_exists R K g I x

/--
[mem_smul_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/GroupAction.lean)
-/
@[path]
private lemma mem_smul_iff_eq
  [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] [IsFractionRing R K] [Group G] [MulSemiringAction G R]
  {g : G}
  {I : FractionalIdeal R⁰ K}
  {x : K} :
-- imply
  x ∈ g • I ↔
    (IsFractionRing.ringEquivOfRingEquiv
    (MulSemiringAction.toRingAut G R g)).symm x ∈ I := by
-- proof
  apply FractionalIdeal.mem_smul_iff R K g I x

/--
[smul_coeIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/GroupAction.lean)
-/
@[path]
private lemma smul_coeIdeal_eq
  [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] [IsFractionRing R K] [Group G] [MulSemiringAction G R]
  {g : G}
  {I : Ideal R} :
-- imply
  g • (I : FractionalIdeal R⁰ K) =
    ((g • I : Ideal R) : FractionalIdeal R⁰ K) := by
-- proof
  apply FractionalIdeal.smul_coeIdeal R K g I


-- created on 2026-10-20
