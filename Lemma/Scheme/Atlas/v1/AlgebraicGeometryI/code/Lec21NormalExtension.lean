import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec21NormalExtension
open AlgebraicHartogs in


/--
[not_le_heightOnePrime_of_height_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec21NormalExtension.lean)
-/
@[path]
lemma not_le_heightOnePrime_of_height_ge_two
  [CommRing A]
  {I : Ideal A}
  {p : HeightOnePrime A}
-- given
  (hI : 2 ≤ I.height) :
-- imply
  ¬(I ≤ p.asIdeal) := by
-- proof
  intro hle
  have h1 : I.height ≤ p.asIdeal.height := Ideal.height_mono hle
  rw [p.height_eq] at h1
  exact absurd (le_trans hI h1) (by norm_num)
namespace Proposition39
section NormalDomain
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]


-- created on 2026-10-23
