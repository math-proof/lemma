import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.RingTheory.FractionalIdeal.GroupAction
open scoped nonZeroDivisors
open scoped Pointwise
open scoped FractionalIdealUnits
open FractionalIdeal


namespace FractionalIdeal

/--
[units_smul_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/GroupAction.lean)
-/
@[path]
lemma units_smul_val
  [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] [IsFractionRing R K] [Group G] [MulSemiringAction G R]
  {g : G}
  {I : (FractionalIdeal R⁰ K)ˣ} :
-- imply
  ((g • I : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) =
    g • (I : FractionalIdeal R⁰ K) :=
-- proof
  rfl

end FractionalIdeal

namespace FractionalIdeal

/--
[smul_def](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/GroupAction.lean)
-/
@[path]
lemma smul_def
  [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] [IsFractionRing R K] [Group G] [MulSemiringAction G R]
  {g : G}
  {I : FractionalIdeal R⁰ K} :
-- imply
  g • I =
    FractionalIdeal.ringEquivOfRingEquiv K K
    (MulSemiringAction.toRingAut G R g) I :=
-- proof
  rfl

end FractionalIdeal

namespace FractionalIdeal

/--
[mem_smul_iff_exists](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/GroupAction.lean)
-/
@[path]
lemma mem_smul_iff_exists
  [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] [IsFractionRing R K] [Group G] [MulSemiringAction G R]
  {g : G}
  {I : FractionalIdeal R⁰ K}
  {x : K} :
-- imply
  x ∈ g • I ↔ ∃ y ∈ I,
    IsFractionRing.ringEquivOfRingEquiv
    (MulSemiringAction.toRingAut G R g) y = x := by
-- proof
  rw [smul_def]
  change x ∈ (ringEquivOfRingEquiv K K (MulSemiringAction.toRingAut G R g) I).val ↔ _
  rw [FractionalIdeal.ringEquivOfRingEquiv_apply_val, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, h⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

end FractionalIdeal

namespace FractionalIdeal

/--
[mem_smul_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/GroupAction.lean)
-/
@[path]
lemma mem_smul_iff
  [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] [IsFractionRing R K] [Group G] [MulSemiringAction G R]
  {g : G}
  {I : FractionalIdeal R⁰ K}
  {x : K} :
-- imply
  x ∈ g • I ↔
    (IsFractionRing.ringEquivOfRingEquiv
    (MulSemiringAction.toRingAut G R g)).symm x ∈ I := by
-- proof
  let F := IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K)
    (MulSemiringAction.toRingAut G R g)
  rw [mem_smul_iff_exists (R := R) (K := K)]
  constructor
  · rintro ⟨y, hy, h⟩
    rwa [← h, F.symm_apply_apply]
  · intro hx
    exact ⟨F.symm x, hx, F.apply_symm_apply x⟩

end FractionalIdeal

namespace FractionalIdeal

/--
[smul_coeIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/GroupAction.lean)
-/
@[path]
lemma smul_coeIdeal
  [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] [IsFractionRing R K] [Group G] [MulSemiringAction G R]
  {g : G}
  {I : Ideal R} :
-- imply
  g • (I : FractionalIdeal R⁰ K) =
    ((g • I : Ideal R) : FractionalIdeal R⁰ K) := by
-- proof
  ext x
  simp only [mem_smul_iff_exists, mem_coeIdeal]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hx⟩
    have h : IsFractionRing.ringEquivOfRingEquiv
      (MulSemiringAction.toRingAut G R g) (algebraMap R K a) =
      algebraMap R K (g • a) := by
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
      rfl
    refine ⟨g • a, Ideal.mem_pointwise_smul_iff_inv_smul_mem.mpr ?_, ?_⟩
    · simpa using ha
    · rw [← hx, h]
  · rintro ⟨b, hb, rfl⟩
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb
    have h : IsFractionRing.ringEquivOfRingEquiv
      (MulSemiringAction.toRingAut G R g) (algebraMap R K (g⁻¹ • b)) =
      algebraMap R K b := by
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
      congr 1
      exact smul_inv_smul g b
    exact ⟨_, ⟨_, hb, rfl⟩, h⟩

end FractionalIdeal


-- created on 2026-10-20
-- updated on 2026-10-26
