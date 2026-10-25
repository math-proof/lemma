import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.CechSheafDataP1.Part3
open CechSheafDataP1
open SerreDualityTate CanonicalSheafCurves GenusConstruction
open TateCechInfra


namespace CechSheafDataP1

/--
[P1_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean)
-/
@[path]
lemma P1_genus
  {k : Type}
  [Field k] :
-- imply
  (P1 k).g = 0 :=
-- proof
  P1CurveFromCech_genus k

end CechSheafDataP1

namespace CechSheafDataP1

/--
[serre_duality_P1_from_cech_data](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean)
-/
@[path]
lemma serre_duality_P1_from_cech_data
  {k : Type}
  [Field k] :
-- imply
  (cechSheafDataP1 k).h0_EK = (cechSheafDataP1 k).h1_E ∧ (cechSheafDataP1 k).h0_E = (cechSheafDataP1 k).h1_EK :=
-- proof
  serre_duality_both (cechSheafDataP1 k)

end CechSheafDataP1

namespace CechSheafDataP1

/--
[serre_duality_P1_h0K_eq_h1O](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean)
-/
@[path]
lemma serre_duality_P1_h0K_eq_h1O
  {k : Type}
  [Field k] :
-- imply
  (cechSheafDataP1 k).h0_EK = (cechSheafDataP1 k).h1_E :=
-- proof
  serre_duality_unconditional (cechSheafDataP1 k)

end CechSheafDataP1

namespace CechSheafDataP1

/--
[serre_duality_P1_h0O_eq_h1K](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean)
-/
@[path]
lemma serre_duality_P1_h0O_eq_h1K
  {k : Type}
  [Field k] :
-- imply
  (cechSheafDataP1 k).h0_E = (cechSheafDataP1 k).h1_EK :=
-- proof
  serre_duality_h0_eq_h1 (cechSheafDataP1 k)

end CechSheafDataP1

namespace CechSheafDataP1

/--
[serre_duality_P1_full_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean)
-/
@[path]
lemma serre_duality_P1_full_chain
  {k : Type}
  [Field k] :
-- imply
  (cechSheafDataP1 k).h0_EK = (cechSheafDataP1 k).h1_E ∧ (cechSheafDataP1 k).h0_E = (cechSheafDataP1 k).h1_EK ∧ (P1 k).χ (1, 0) + (P1 k).χ (1, (P1 k).degK - 0) = 0 :=
-- proof
  serre_duality_full_chain (cechSheafDataP1 k)

end CechSheafDataP1

namespace CechSheafDataP1

/--
[cechSheafDataP1_nonvacuity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean)
-/
@[path]
lemma cechSheafDataP1_nonvacuity
  {k : Type}
  [Field k] :
-- imply
  Nonempty (CechSheafData.{0} k) :=
-- proof
  ⟨cechSheafDataP1 k⟩

end CechSheafDataP1

namespace CechSheafDataP1

/--
[cechSheafDataP1_values](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean)
-/
@[path]
lemma cechSheafDataP1_values
  {k : Type}
  [Field k] :
-- imply
  (cechSheafDataP1 k).h0_E = 1 ∧ (cechSheafDataP1 k).h1_EK = 1 ∧ (cechSheafDataP1 k).deg = 0 ∧ (cechSheafDataP1 k).curve.g = 0 ∧ (cechSheafDataP1 k).curve.degK = -2 :=
-- proof
  ⟨rfl, rfl, rfl, P1_genus k, P1_degK k⟩

end CechSheafDataP1

namespace CechSheafDataP1

/--
[cechSheafDataP1_cech_dimensions](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean)
-/
@[path]
lemma cechSheafDataP1_cech_dimensions
  {k : Type}
  [Field k] :
-- imply
  Module.finrank k (cechSheafDataP1 k).setup.cechH1 = 0 ∧ Module.finrank k ↥(cechSheafDataP1 k).setup.dual.cechH0 = 0 :=
-- proof
  ⟨finrank_cechH1_eq_zero k, finrank_dual_cechH0_eq_zero k⟩

end CechSheafDataP1

namespace CechSheafDataP1

/--
[serre_duality_P1_concrete_values](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean)
-/
@[path]
lemma serre_duality_P1_concrete_values
  {k : Type}
  [Field k] :
-- imply
  (cechSheafDataP1 k).h0_EK = 0 ∧ (cechSheafDataP1 k).h1_E = 0 := by
-- proof
  constructor
  ·
    show (Module.finrank k ↥(tateSetupP1 k).dual.cechH0 : ℤ) = 0
    rw [finrank_dual_cechH0_eq_zero]
    simp
  ·
    show (Module.finrank k (tateSetupP1 k).cechH1 : ℤ) = 0
    rw [finrank_cechH1_eq_zero]
    simp
end CechSheafDataP1


/--
[finrank_cechH1_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean)
-/
@[path]
private lemma finrank_cechH1_eq_zero_eq
  {k : Type}
  [Field k] :
-- imply
  Module.finrank k (tateSetupP1 k).cechH1 = 0 := by
-- proof
  apply CechSheafDataP1.finrank_cechH1_eq_zero k

/--
[finrank_dual_cechH0_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean)
-/
@[path]
private lemma finrank_dual_cechH0_eq_zero_eq
  {k : Type}
  [Field k] :
-- imply
  Module.finrank k ↥(tateSetupP1 k).dual.cechH0 = 0 := by
-- proof
  apply CechSheafDataP1.finrank_dual_cechH0_eq_zero k

/--
[P1_degK](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean)
-/
@[path]
private lemma P1_degK_eq
  {k : Type}
  [Field k] :
-- imply
  (P1 k).degK = -2 := by
-- proof
  apply CechSheafDataP1.P1_degK k

/--
[P1_chi_O](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean)
-/
@[path]
private lemma P1_chi_O_eq
  {k : Type}
  [Field k] :
-- imply
  (P1 k).χ (1, 0) = 1 := by
-- proof
  apply CechSheafDataP1.P1_chi_O k

/--
[P1_chi_K](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean)
-/
@[path]
private lemma P1_chi_K_eq
  {k : Type}
  [Field k] :
-- imply
  (P1 k).χ (1, -2) = -1 := by
-- proof
  apply CechSheafDataP1.P1_chi_K k


-- created on 2026-10-23
