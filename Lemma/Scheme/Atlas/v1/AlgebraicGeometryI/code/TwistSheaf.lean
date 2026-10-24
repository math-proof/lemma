import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.TwistSheaf
open MvPolynomial QCohProjective TwistSheaf


namespace TwistSheaf

/--
[polyGrSub_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma polyGrSub_nonneg
  {k : Type*}
  [Field k]
  {n : ℕ}
  {d : ℤ}
-- given
  (hd : 0 ≤ d) :
-- imply
  polyGrSub k n d = homogeneousSubmodule (Fin (n + 1)) k d.toNat :=
-- proof
  if_pos hd

end TwistSheaf

namespace TwistSheaf

/--
[polyGrSub_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma polyGrSub_neg
  {k : Type*}
  [Field k]
  {n : ℕ}
  {d : ℤ}
-- given
  (hd : d < 0) :
-- imply
  polyGrSub k n d = ⊥ :=
-- proof
  if_neg (by omega)

end TwistSheaf

namespace TwistSheaf

/--
[polyGrComp_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma polyGrComp_nat
  {k : Type*}
  [Field k]
  {n : ℕ}
  {d : ℕ} :
-- imply
  polyGrComp k n (d : ℤ) = ↥(homogeneousSubmodule (Fin (n + 1)) k d) := by
-- proof
  show ↥(polyGrSub k n ↑d) = ↥(homogeneousSubmodule (Fin (n + 1)) k d)
  rw [polyGrSub_nonneg k n ↑d (Int.natCast_nonneg d), Int.toNat_natCast]

end TwistSheaf

namespace TwistSheaf

/--
[serreTwist_zero_component](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma serreTwist_zero_component
  {k : Type*}
  [Field k]
  {n : ℕ}
  {i : ℤ} :
-- imply
  (serreTwist k n 0).component i = (structureSheafData k n).component i := by
-- proof
  simp [serreTwist, GradedModuleData.twist]

end TwistSheaf

namespace TwistSheaf

/--
[serreTwist_double](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma serreTwist_double
  {k : Type*}
  [Field k]
  {n : ℕ}
  {d₁ d₂ : ℤ}
  {i : ℤ} :
-- imply
  ((serreTwist k n d₁).twist d₂).component i = (serreTwist k n (d₁ + d₂)).component i := by
-- proof
  simp [serreTwist, GradedModuleData.twist, add_assoc, add_comm d₂ d₁]

end TwistSheaf

namespace TwistSheaf

/--
[serreTwist_neg_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma serreTwist_neg_cancel
  {k : Type*}
  [Field k]
  {n : ℕ}
  {d : ℤ}
  {i : ℤ} :
-- imply
  ((serreTwist k n d).twist (-d)).component i = (structureSheafData k n).component i := by
-- proof
  simp [serreTwist, GradedModuleData.twist, add_assoc]

end TwistSheaf

namespace TwistSheaf

/--
[globalSections_serreTwist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma globalSections_serreTwist
  {k : Type*}
  [Field k]
  {n : ℕ}
  {d : ℤ} :
-- imply
  (serreTwist k n d).component 0 = (structureSheafData k n).component d := by
-- proof
  simp [serreTwist, GradedModuleData.twist]

end TwistSheaf

namespace TwistSheaf

/--
[globalSections_serreTwist_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma globalSections_serreTwist_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {d : ℕ} :
-- imply
  (serreTwist k n (d : ℤ)).component 0 = ↥(homogeneousSubmodule (Fin (n + 1)) k d) := by
-- proof
  trans (structureSheafData k n).component ↑d
  · exact globalSections_serreTwist k n ↑d
  · exact polyGrComp_nat k n d

end TwistSheaf

namespace TwistSheaf

/--
[serreTwist_globalSections_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma serreTwist_globalSections_finrank
  {k : Type*}
  [Field k]
  {n : ℕ}
  {d : ℕ} :
-- imply
  Module.finrank k ↥(homogeneousSubmodule (Fin (n + 1)) k d) = (n + d).choose n :=
-- proof
  globalSections_Od_finrank k n d

end TwistSheaf

namespace TwistSheaf

/--
[serreTwist_globalSections_finrank_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma serreTwist_globalSections_finrank_symm
  {k : Type*}
  [Field k]
  {n : ℕ}
  {d : ℕ} :
-- imply
  Module.finrank k ↥(homogeneousSubmodule (Fin (n + 1)) k d) = (n + d).choose d := by
-- proof
  rwa [serreTwist_globalSections_finrank]

end TwistSheaf

namespace TwistSheaf

/--
[globalSections_O0_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma globalSections_O0_finrank
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  Module.finrank k ↥(homogeneousSubmodule (Fin (n + 1)) k 0) = 1 := by
-- proof
  rw [serreTwist_globalSections_finrank]
  simp

end TwistSheaf

namespace TwistSheaf

/--
[globalSections_O1_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma globalSections_O1_finrank
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  Module.finrank k ↥(homogeneousSubmodule (Fin (n + 1)) k 1) = n + 1 := by
-- proof
  rw [serreTwist_globalSections_finrank]
  simp

end TwistSheaf

namespace TwistSheaf

/--
[twist_shift_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma twist_shift_add
  {k : Type*}
  [Field k]
  {n : ℕ}
  {d₁ d₂ : ℤ}
  {i : ℤ} :
-- imply
  (serreTwist k n (d₁ + d₂)).component i = ((serreTwist k n d₁).twist d₂).component i := by
-- proof
  simp [serreTwist, GradedModuleData.twist, add_assoc, add_comm d₂ d₁]

end TwistSheaf

namespace TwistSheaf

/--
[picard_group_twist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma picard_group_twist
  {k : Type*}
  [Field k]
  {n : ℕ}
  {d₁ d₂ : ℤ}
  {i : ℤ} :
-- imply
  (serreTwist k n (d₁ + d₂)).component i = ((serreTwist k n d₁).twist d₂).component i :=
-- proof
  twist_shift_add k n d₁ d₂ i

end TwistSheaf

namespace TwistSheaf

/--
[globalSections_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma globalSections_mono
  {k : Type*}
  [Field k]
  {n : ℕ}
  {d : ℕ} :
-- imply
  Module.finrank k ↥(homogeneousSubmodule (Fin (n + 1)) k d) ≤ Module.finrank k ↥(homogeneousSubmodule (Fin (n + 1)) k (d + 1)) := by
-- proof
  rw [serreTwist_globalSections_finrank, serreTwist_globalSections_finrank]
  exact Nat.choose_le_choose n (by omega)

end TwistSheaf

namespace TwistSheaf

/--
[globalSections_negative_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean)
-/
@[path]
lemma globalSections_negative_trivial
  {k : Type*}
  [Field k]
  {n : ℕ}
  {d : ℤ}
-- given
  (hd : d < 0) :
-- imply
  polyGrSub k n d = ⊥ :=
-- proof
  polyGrSub_neg k n d hd
end TwistSheaf



-- created on 2026-10-23
