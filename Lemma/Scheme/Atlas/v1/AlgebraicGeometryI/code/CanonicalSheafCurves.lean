import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
open RiemannRochCurves CanonicalSheafCurves


namespace CanonicalSheafCurves

/--
[chi_eq_rr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean)
-/
@[path]
lemma chi_eq_rr
  {C : SmoothCompleteCurve}
  {r d : ℤ} :
-- imply
  C.χ (r, d) = d - r * (C.g - 1) :=
-- proof
  riemann_roch_curves_thm C.g C.χ C.hχ_struct C.hχ_sky r d

end CanonicalSheafCurves

namespace CanonicalSheafCurves

/--
[chi_canonical_by_rr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean)
-/
@[path]
lemma chi_canonical_by_rr
  {C : SmoothCompleteCurve} :
-- imply
  C.χ (1, C.degK) = C.degK + 1 - C.g := by
-- proof
  rw [chi_eq_rr C 1 C.degK]; ring

end CanonicalSheafCurves

namespace CanonicalSheafCurves

/--
[deg_canonical_P1_check](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean)
-/
@[path]
lemma deg_canonical_P1_check
-- imply
  2 * (0 : ℤ) - 2 = -2 := by
-- proof
norm_num

end CanonicalSheafCurves

namespace CanonicalSheafCurves

/--
[deg_canonical_elliptic_check](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean)
-/
@[path]
lemma deg_canonical_elliptic_check
-- imply
  2 * (1 : ℤ) - 2 = 0 := by
-- proof
norm_num

end CanonicalSheafCurves

namespace CanonicalSheafCurves

/--
[deg_canonical_genus2_check](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean)
-/
@[path]
lemma deg_canonical_genus2_check
-- imply
  2 * (2 : ℤ) - 2 = 2 := by
-- proof
norm_num

end CanonicalSheafCurves

namespace CanonicalSheafCurves

/--
[chi_symmetry](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean)
-/
@[path]
lemma chi_symmetry
  {C : SmoothCompleteCurve} :
-- imply
  (1 - C.g) + (C.g - 1) = 0 := by
-- proof
ring

end CanonicalSheafCurves

namespace CanonicalSheafCurves

/--
[adjunction_genus_plane_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean)
-/
@[path]
lemma adjunction_genus_plane_curve
  {d : ℤ} :
-- imply
  d * (d - 3) + 2 = (d - 1) * (d - 2) := by
-- proof
ring

end CanonicalSheafCurves

namespace CanonicalSheafCurves

/--
[adjunction_genus_plane_curve_degK](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean)
-/
@[path]
lemma adjunction_genus_plane_curve_degK
  {d : ℤ}
-- given
  (_hd : 0 ≤ d) :
-- imply
  let g := (d - 1) * (d - 2) / 2 2 * g - 2 = d * (d - 3) := by
-- proof
  intro g
  have h_even : (2 : ℤ) ∣ (d - 1) * (d - 2) := by
    obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Int.even_or_odd d
    · exact ⟨(d - 1) * (m - 1), by rw [hm]; ring⟩
    · exact ⟨m * (d - 2), by rw [hm]; ring⟩
  rw [show g = (d - 1) * (d - 2) / 2 from rfl, Int.mul_ediv_cancel' h_even]
  ring
/-- Consistency with the Euler-sequence calculation on `P^1`: `deg K_{P^1} = -(1 + 1) = -2`. -/
end CanonicalSheafCurves


/--
[curveWitness_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean)
-/
@[path]
private lemma curveWitness_zero_eq :
-- imply
  CurveWitness 0 := by
-- proof
  apply CanonicalSheafCurves.curveWitness_zero


-- created on 2026-10-23
