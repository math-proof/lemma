import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRoch
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRoch
open RiemannRoch


/--
[riemann_roch_line_bundle_p1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityGeneral.lean)
-/
@[path]
lemma riemann_roch_line_bundle_p1
  {k : Type}
  [Field k]
  {d : ℤ} :
-- imply
  (dimH0 k d : ℤ) - (dimH1 k d : ℤ) = d + 1 :=
-- proof
  riemann_roch_P1 k d

/--
[serre_duality_classical_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityGeneral.lean)
-/
@[path]
lemma serre_duality_classical_P1
  {k : Type}
  [Field k]
  {d : ℤ} :
-- imply
  (dimH0 k d : ℤ) - (dimH0 k (-2 - d) : ℤ) = d + 1 :=
-- proof
  riemann_roch_serre_form k d

/--
[genus_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityGeneral.lean)
-/
@[path]
lemma genus_P1
  {k : Type}
  [Field k] :
-- imply
  dimH1 k 0 = 0 := by
-- proof
  rw [show (0 : ℤ) = ↑(0 : ℕ) from rfl]; exact dimH1_nonneg k 0

/--
[arithmetic_eq_geometric_genus_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityGeneral.lean)
-/
@[path]
lemma arithmetic_eq_geometric_genus_P1
  {k : Type}
  [Field k] :
-- imply
  dimH1 k 0 = dimH0 k (-2) := by
-- proof
  rw [show (0 : ℤ) = ↑(0 : ℕ) from rfl, dimH1_nonneg, dimH0_neg k (-2) (by norm_num)]

/--
[deg_canonical_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityGeneral.lean)
-/
@[path]
lemma deg_canonical_P1
-- imply
  ((-2 : ℤ) = 2 * 0 - 2) := by
-- proof
ring

/--
[dimH0_ge_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityGeneral.lean)
-/
@[path]
lemma dimH0_ge_P1
  {k : Type}
  [Field k]
  {d : ℤ} :
-- imply
  (dimH0 k d : ℤ) ≥ d + 1 - 0 := by
-- proof
  linarith [riemann_roch_P1 k d, show (dimH1 k d : ℤ) ≥ 0 from Int.natCast_nonneg _]

/--
[cech_duality_dimension_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityGeneral.lean)
-/
@[path]
lemma cech_duality_dimension_P1
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  dimH1 k n = dimH0 k (-2 - n) :=
-- proof
  serre_duality_P1 k n


-- created on 2026-10-23
