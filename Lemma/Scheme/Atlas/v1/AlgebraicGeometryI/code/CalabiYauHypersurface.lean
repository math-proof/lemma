import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CalabiYauHypersurface
open CYHyp SmoothProjectiveHypersurface


namespace CYHyp

/--
[mkCurve'_elliptic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma mkCurve'_elliptic
-- imply
  (mkCurve' 1).degK = 0 := by
-- proof
norm_num [mkCurve']

end CYHyp

namespace SmoothProjectiveHypersurface

/--
[adjunction_formula_hypersurface](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma adjunction_formula_hypersurface
  {Y : SmoothProjectiveHypersurface} :
-- imply
  Y.canonicalTwist = (Y.d : ℤ) - (Y.n : ℤ) - 1 :=
-- proof
  rfl

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[canonicalTwist_from_euler](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma canonicalTwist_from_euler
  {Y : SmoothProjectiveHypersurface} :
-- imply
  Y.canonicalTwist = -((Y.n : ℤ) + 1) + (Y.d : ℤ) := by
-- proof
  simp only [canonicalTwist]; ring

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[adjunction_formula_from_euler_and_normal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma adjunction_formula_from_euler_and_normal
  {Y : SmoothProjectiveHypersurface} :
-- imply
  Y.canonicalTwist = (-(↑Y.n + 1) : ℤ) + (↑Y.d : ℤ) := by
-- proof
  simp only [canonicalTwist]; ring

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[degCanonical_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma degCanonical_eq
  {Y : SmoothProjectiveHypersurface} :
-- imply
  Y.degCanonical = (Y.d : ℤ) * ((Y.d : ℤ) - (Y.n : ℤ) - 1) :=
-- proof
  rfl

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[degCanonical_expand](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma degCanonical_expand
  {Y : SmoothProjectiveHypersurface} :
-- imply
  Y.degCanonical = (Y.d : ℤ) ^ 2 - (Y.d : ℤ) * ((Y.n : ℤ) + 1) := by
-- proof
  simp only [degCanonical, canonicalTwist]; ring

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[canonicalTwist_zero_iff_calabiYau](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma canonicalTwist_zero_iff_calabiYau
  {Y : SmoothProjectiveHypersurface} :
-- imply
  Y.canonicalTwist = 0 ↔ Y.isCalabiYau := by
-- proof
  constructor
  · intro h; simp only [canonicalTwist, isCalabiYau] at *; omega
  · intro h; simp only [canonicalTwist, isCalabiYau] at *; omega

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[degCanonical_zero_of_calabiYau](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma degCanonical_zero_of_calabiYau
  {Y : SmoothProjectiveHypersurface}
-- given
  (h : Y.isCalabiYau) :
-- imply
  Y.degCanonical = 0 := by
-- proof
  simp only [degCanonical]
  rw [(canonicalTwist_zero_iff_calabiYau Y).mpr h, mul_zero]

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[calabiYau_of_degCanonical_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma calabiYau_of_degCanonical_zero
  {Y : SmoothProjectiveHypersurface}
-- given
  (h : Y.degCanonical = 0) :
-- imply
  Y.isCalabiYau := by
-- proof
  simp only [degCanonical, canonicalTwist] at h
  have hd_pos : (Y.d : ℤ) ≠ 0 := by have := Y.hd; omega
  obtain h1 | h1 := mul_eq_zero.mp h
  · exact absurd h1 hd_pos
  · simp only [isCalabiYau]
    have : (Y.d : ℤ) - (Y.n : ℤ) - 1 = 0 := h1
    omega

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[ellipticCurve_isCalabiYau](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma ellipticCurve_isCalabiYau
-- imply
  ellipticCurve.isCalabiYau := by
-- proof
  unfold isCalabiYau ellipticCurve; rfl

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[K3surface_isCalabiYau](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma K3surface_isCalabiYau
-- imply
  K3surface.isCalabiYau := by
-- proof
  unfold isCalabiYau K3surface; rfl

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[CY3fold_isCalabiYau](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma CY3fold_isCalabiYau
-- imply
  CY3fold.isCalabiYau := by
-- proof
  unfold isCalabiYau CY3fold; rfl

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[ellipticCurve_canonicalTwist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma ellipticCurve_canonicalTwist
-- imply
  ellipticCurve.canonicalTwist = 0 := by
-- proof
  simp [canonicalTwist, ellipticCurve]

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[ellipticCurve_degCanonical_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma ellipticCurve_degCanonical_zero
-- imply
  ellipticCurve.degCanonical = 0 :=
-- proof
  degCanonical_zero_of_calabiYau _ ellipticCurve_isCalabiYau

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[K3surface_degCanonical_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma K3surface_degCanonical_zero
-- imply
  K3surface.degCanonical = 0 :=
-- proof
  degCanonical_zero_of_calabiYau _ K3surface_isCalabiYau

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[calabiYau_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma calabiYau_general
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  let Y : SmoothProjectiveHypersurface := { n := n, d := n + 1, hn := hn, hd := by omega } Y.canonicalTwist = 0 := by
-- proof
  simp [canonicalTwist]

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[degCanonical_plane_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma degCanonical_plane_curve
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  let Y : SmoothProjectiveHypersurface := { n := 2, d := d, hn := by omega, hd := hd } Y.degCanonical = (d : ℤ) * ((d : ℤ) - 3) := by
-- proof
  simp only [degCanonical, canonicalTwist]
  ring

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[genus_from_adjunction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma genus_from_adjunction
  {d : ℕ}
  {g : ℤ}
-- given
  (hd : 1 ≤ d)
  (hg : 2 * g - 2 = (SmoothProjectiveHypersurface.mk 2 d (by omega) hd).degCanonical) :
-- imply
  2 * g = ((d : ℤ) - 1) * ((d : ℤ) - 2) := by
-- proof
  simp only [degCanonical, canonicalTwist] at hg
  push_cast at hg ⊢
  nlinarith

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[degCanonical_line](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma degCanonical_line
-- imply
  (mk 2 1 (by omega) (by omega)).degCanonical = -2 := by
-- proof
  simp [degCanonical, canonicalTwist]

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[degCanonical_conic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma degCanonical_conic
-- imply
  (mk 2 2 (by omega) (by omega)).degCanonical = -2 := by
-- proof
  simp [degCanonical, canonicalTwist]

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[degCanonical_cubic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma degCanonical_cubic
-- imply
  (mk 2 3 (by omega) (by omega)).degCanonical = 0 := by
-- proof
  simp [degCanonical, canonicalTwist]

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[degCanonical_quartic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma degCanonical_quartic
-- imply
  (mk 2 4 (by omega) (by omega)).degCanonical = 4 := by
-- proof
  simp [degCanonical, canonicalTwist]

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[elliptic_degK_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma elliptic_degK_consistent
-- imply
  ellipticCurve.degCanonical = 0 ∧ (mkCurve' 1).degK = 0 :=
-- proof
  ⟨ellipticCurve_degCanonical_zero, mkCurve'_elliptic⟩

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[degK_hypersurface_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma degK_hypersurface_formula
  {n d : ℤ} :
-- imply
  degK_hypersurface n d = d * (d - (n + 1)) :=
-- proof
  rfl

end SmoothProjectiveHypersurface

namespace SmoothProjectiveHypersurface

/--
[degCanonical_eq_degK_hypersurface](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
lemma degCanonical_eq_degK_hypersurface
  {Y : SmoothProjectiveHypersurface} :
-- imply
  Y.degCanonical = degK_hypersurface (Y.n : ℤ) (Y.d : ℤ) := by
-- proof
  simp only [degCanonical, degK_hypersurface, canonicalTwist]; ring
end SmoothProjectiveHypersurface


/--
[mkCurve'_degK](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean)
-/
@[path]
private lemma mkCurve'_degK_eq
  {g : ℕ} :
-- imply
  (mkCurve' g).degK = 2 * (g : ℤ) - 2 := by
-- proof
  apply CYHyp.mkCurve'_degK g


-- created on 2026-10-23
