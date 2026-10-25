import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.GrothendieckBirkhoff
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GrothendieckBirkhoff
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
open GrothendieckBirkhoff CanonicalSheafCurves


namespace GenusPlaneAdjunctionBridge

/--
[two_dvd_shifted_product](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusPlaneAdjunctionBridge.lean)
-/
@[path]
lemma two_dvd_shifted_product
  {d : ℕ} :
-- imply
  2 ∣ (d - 1) * (d - 2) := by
-- proof
  obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Nat.even_or_odd (d - 1)
  · exact ⟨m * (d - 2), by rw [hm]; ring⟩
  · have hd2 : d - 2 = m + m := by omega
    exact ⟨(d - 1) * m, by rw [hd2]; ring⟩

end GenusPlaneAdjunctionBridge

namespace GenusPlaneAdjunctionBridge

/--
[two_mul_genus_plane_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusPlaneAdjunctionBridge.lean)
-/
@[path]
lemma two_mul_genus_plane_curve
  {d : ℕ} :
-- imply
  2 * genus_plane_curve d = (d - 1) * (d - 2) :=
-- proof
  Nat.mul_div_cancel' (two_dvd_shifted_product d)

end GenusPlaneAdjunctionBridge

namespace GenusPlaneAdjunctionBridge

/--
[two_mul_genus_plane_curve_int](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusPlaneAdjunctionBridge.lean)
-/
@[path]
lemma two_mul_genus_plane_curve_int
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  2 * ((genus_plane_curve d : ℕ) : ℤ) = ((d : ℤ) - 1) * ((d : ℤ) - 2) := by
-- proof
  have _h1 : 1 ≤ d := by omega
  exact_mod_cast two_mul_genus_plane_curve d

end GenusPlaneAdjunctionBridge

namespace GenusPlaneAdjunctionBridge

/--
[adjunction_chain_two_g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusPlaneAdjunctionBridge.lean)
-/
@[path]
lemma adjunction_chain_two_g
  {d g : ℤ}
-- given
  (hdegK : d * (d - 3) = 2 * g - 2) :
-- imply
  2 * g = (d - 1) * (d - 2) := by
-- proof
  linarith [show d * (d - 3) + 2 = (d - 1) * (d - 2) from by ring]

end GenusPlaneAdjunctionBridge

namespace GenusPlaneAdjunctionBridge

/--
[adjunction_chain_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusPlaneAdjunctionBridge.lean)
-/
@[path]
lemma adjunction_chain_genus
  {d g : ℤ}
-- given
  (h : 2 * g = (d - 1) * (d - 2)) :
-- imply
  g = (d - 1) * (d - 2) / 2 := by
-- proof
  have h2 : (2 : ℤ) ≠ 0 := by norm_num
  rw [← h, Int.mul_ediv_cancel_left g h2]

end GenusPlaneAdjunctionBridge

namespace GenusPlaneAdjunctionBridge

/--
[adjunction_chain_degK_to_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusPlaneAdjunctionBridge.lean)
-/
@[path]
lemma adjunction_chain_degK_to_genus
  {d g : ℤ}
-- given
  (hdegK : d * (d - 3) = 2 * g - 2) :
-- imply
  g = (d - 1) * (d - 2) / 2 :=
-- proof
  adjunction_chain_genus d g (adjunction_chain_two_g d g hdegK)

end GenusPlaneAdjunctionBridge

namespace GenusPlaneAdjunctionBridge

/--
[genus_plane_curve_eq_adjunction_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusPlaneAdjunctionBridge.lean)
-/
@[path]
lemma genus_plane_curve_eq_adjunction_genus
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  ((genus_plane_curve d : ℕ) : ℤ) = ((d : ℤ) - 1) * ((d : ℤ) - 2) / 2 := by
-- proof
  have h := two_mul_genus_plane_curve_int d hd
  have h2 : (2 : ℤ) ≠ 0 := by norm_num
  rw [← Int.mul_ediv_cancel_left ((genus_plane_curve d : ℕ) : ℤ) h2]
  rw [h]

end GenusPlaneAdjunctionBridge


-- created on 2026-10-23
