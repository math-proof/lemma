import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityLinear.Part4
open SerreDualityP1
open CohomologyP1


namespace SerreDualityP1

/--
[residueShift_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean)
-/
@[path]
lemma residueShift_involutive
-- imply
  Function.Involutive residueShift := by
-- proof
  intro i; simp [residueShift]

end SerreDualityP1

namespace SerreDualityP1

/--
[residueShift_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean)
-/
@[path]
lemma residueShift_injective
-- imply
  Function.Injective residueShift :=
-- proof
  residueShift_involutive.injective

end SerreDualityP1

namespace SerreDualityP1

/--
[serre_duality_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean)
-/
@[path]
lemma serre_duality_finrank
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : n < -1) :
-- imply
  Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) = Module.finrank k ↥(CechH0 k (-2 - n)) :=
-- proof
  (serre_duality_P1 k n hn).finrank_eq

end SerreDualityP1

namespace SerreDualityP1

/--
[residueShift_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean)
-/
@[path]
lemma residueShift_zero
-- imply
  residueShift 0 = -1 := by
-- proof
simp [residueShift]

end SerreDualityP1

namespace SerreDualityP1

/--
[residueShift_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean)
-/
@[path]
lemma residueShift_neg_one
-- imply
  residueShift (-1) = 0 := by
-- proof
simp [residueShift]

end SerreDualityP1

namespace SerreDualityP1

/--
[residueShift_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean)
-/
@[path]
lemma residueShift_add
  {i : ℤ} :
-- imply
  residueShift i + i = -1 := by
-- proof
  simp [residueShift]

end SerreDualityP1

namespace SerreDualityP1

/--
[residueShift_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean)
-/
@[path]
lemma residueShift_antitone
-- imply
  Antitone residueShift := by
-- proof
  intro a b hab; simp [residueShift]; omega

end SerreDualityP1

/--
[residueShift_comp_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean)
-/
@[path]
private lemma residueShift_comp_self_eq :
-- imply
  residueShift ∘ residueShift = id := by
-- proof
  apply SerreDualityP1.residueShift_comp_self

/--
[shiftMap_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean)
-/
@[path]
private lemma shiftMap_involutive_eq
  {k : Type*}
  [Field k] :
-- imply
  Function.Involutive (shiftMap k) := by
-- proof
  apply SerreDualityP1.shiftMap_involutive k

/--
[shiftEquiv_coe_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean)
-/
@[path]
private lemma shiftEquiv_coe_eq_eq
  {k : Type*}
  [Field k] :
-- imply
  (shiftEquiv k : (ℤ →₀ k) →ₗ[k] (ℤ →₀ k)) = shiftMap k := by
-- proof
  apply SerreDualityP1.shiftEquiv_coe_eq k

/--
[residueShift_image_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean)
-/
@[path]
private lemma residueShift_image_Ioo_eq
  {n : ℤ} :
-- imply
  residueShift '' (Set.Ioo n 0) = Set.Icc 0 (-2 - n) := by
-- proof
  apply SerreDualityP1.residueShift_image_Ioo n

/--
[shiftMap_supported_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean)
-/
@[path]
private lemma shiftMap_supported_Ioo_eq
  {k : Type*}
  [Field k]
  {n : ℤ} :
-- imply
  Submodule.map (shiftMap k) (Finsupp.supported k k (Set.Ioo n 0)) = Finsupp.supported k k (Set.Icc 0 (-2 - n)) := by
-- proof
  apply SerreDualityP1.shiftMap_supported_Ioo k n


-- created on 2026-10-23
