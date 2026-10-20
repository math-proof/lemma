import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.CaseyTheoremCyclicOrder
open MetaMathlibExt


/--
[casey_theorem_cyclic_order_core](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/CaseyTheoremCyclicOrder.lean)
-/
@[path]
private lemma casey_theorem_cyclic_order_core_eq
  {O c1 c2 c3 c4 : EuclideanSpace ℝ (Fin 2)}
  {R r1 r2 r3 r4 t12 t23 t34 t41 t13 t24 θ1 θ2 θ3 θ4 : ℝ}
-- given
  (hlt1 : r1 < R)
  (hlt2 : r2 < R)
  (hlt3 : r3 < R)
  (hlt4 : r4 < R)
  (hinner1 : dist c1 O + r1 = R)
  (hinner2 : dist c2 O + r2 = R)
  (hinner3 : dist c3 O + r3 = R)
  (hinner4 : dist c4 O + r4 = R)
  (ht12 : t12 ^ 2 = dist c1 c2 ^ 2 - (r1 - r2) ^ 2)
  (ht23 : t23 ^ 2 = dist c2 c3 ^ 2 - (r2 - r3) ^ 2)
  (ht34 : t34 ^ 2 = dist c3 c4 ^ 2 - (r3 - r4) ^ 2)
  (ht41 : t41 ^ 2 = dist c4 c1 ^ 2 - (r4 - r1) ^ 2)
  (ht13 : t13 ^ 2 = dist c1 c3 ^ 2 - (r1 - r3) ^ 2)
  (ht24 : t24 ^ 2 = dist c2 c4 ^ 2 - (r2 - r4) ^ 2)
  (ht12pos : 0 < t12)
  (ht23pos : 0 < t23)
  (ht34pos : 0 < t34)
  (ht41pos : 0 < t41)
  (ht13pos : 0 < t13)
  (ht24pos : 0 < t24)
  (hθ12 : θ1 < θ2)
  (hθ23 : θ2 < θ3)
  (hθ34 : θ3 < θ4)
  (hθ41 : θ4 < θ1 + 2 * Real.pi)
  (hc1 : c1 - O = dist c1 O • !₂[Real.cos θ1, Real.sin θ1])
  (hc2 : c2 - O = dist c2 O • !₂[Real.cos θ2, Real.sin θ2])
  (hc3 : c3 - O = dist c3 O • !₂[Real.cos θ3, Real.sin θ3])
  (hc4 : c4 - O = dist c4 O • !₂[Real.cos θ4, Real.sin θ4]) :
-- imply
  t12 * t34 + t23 * t41 = t13 * t24 := by
-- proof
  apply MetaMathlibExt.casey_theorem_cyclic_order_core hlt1 hlt2 hlt3 hlt4 hinner1 hinner2 hinner3 hinner4 ht12 ht23 ht34 ht41 ht13 ht24 ht12pos ht23pos ht34pos ht41pos ht13pos ht24pos hθ12 hθ23 hθ34 hθ41 hc1 hc2 hc3 hc4

/--
[casey_theorem_cyclic_order](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/CaseyTheoremCyclicOrder.lean)
-/
@[path]
private lemma casey_theorem_cyclic_order_eq
  {O c1 c2 c3 c4 : EuclideanSpace ℝ (Fin 2)}
  {R r1 r2 r3 r4 t12 t23 t34 t41 t13 t24 θ1 θ2 θ3 θ4 : ℝ}
-- given
  (hR : 0 < R)
  (hr1 : 0 < r1)
  (hr2 : 0 < r2)
  (hr3 : 0 < r3)
  (hr4 : 0 < r4)
  (hlt1 : r1 < R)
  (hlt2 : r2 < R)
  (hlt3 : r3 < R)
  (hlt4 : r4 < R)
  (hinner1 : dist c1 O + r1 = R)
  (hinner2 : dist c2 O + r2 = R)
  (hinner3 : dist c3 O + r3 = R)
  (hinner4 : dist c4 O + r4 = R)
  (hdisj12 : r1 + r2 < dist c1 c2)
  (hdisj23 : r2 + r3 < dist c2 c3)
  (hdisj34 : r3 + r4 < dist c3 c4)
  (hdisj41 : r4 + r1 < dist c4 c1)
  (hdisj13 : r1 + r3 < dist c1 c3)
  (hdisj24 : r2 + r4 < dist c2 c4)
  (ht12 : t12 ^ 2 = dist c1 c2 ^ 2 - (r1 - r2) ^ 2)
  (ht23 : t23 ^ 2 = dist c2 c3 ^ 2 - (r2 - r3) ^ 2)
  (ht34 : t34 ^ 2 = dist c3 c4 ^ 2 - (r3 - r4) ^ 2)
  (ht41 : t41 ^ 2 = dist c4 c1 ^ 2 - (r4 - r1) ^ 2)
  (ht13 : t13 ^ 2 = dist c1 c3 ^ 2 - (r1 - r3) ^ 2)
  (ht24 : t24 ^ 2 = dist c2 c4 ^ 2 - (r2 - r4) ^ 2)
  (ht12pos : 0 < t12)
  (ht23pos : 0 < t23)
  (ht34pos : 0 < t34)
  (ht41pos : 0 < t41)
  (ht13pos : 0 < t13)
  (ht24pos : 0 < t24)
  (hθ12 : θ1 < θ2)
  (hθ23 : θ2 < θ3)
  (hθ34 : θ3 < θ4)
  (hθ41 : θ4 < θ1 + 2 * Real.pi)
  (hc1 : c1 - O = dist c1 O • !₂[Real.cos θ1, Real.sin θ1])
  (hc2 : c2 - O = dist c2 O • !₂[Real.cos θ2, Real.sin θ2])
  (hc3 : c3 - O = dist c3 O • !₂[Real.cos θ3, Real.sin θ3])
  (hc4 : c4 - O = dist c4 O • !₂[Real.cos θ4, Real.sin θ4]) :
-- imply
  t12 * t34 + t23 * t41 = t13 * t24 := by
-- proof
  apply MetaMathlibExt.casey_theorem_cyclic_order hR hr1 hr2 hr3 hr4 hlt1 hlt2 hlt3 hlt4 hinner1 hinner2 hinner3 hinner4 hdisj12 hdisj23 hdisj34 hdisj41 hdisj13 hdisj24 ht12 ht23 ht34 ht41 ht13 ht24 ht12pos ht23pos ht34pos ht41pos ht13pos ht24pos hθ12 hθ23 hθ34 hθ41 hc1 hc2 hc3 hc4


-- created on 2026-10-20
