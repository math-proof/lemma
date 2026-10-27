import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.LieGroups.code.SL2RepWired
open SL2GKModule


namespace SL2GKModule

/--
[ktypeBoundedness_eq_boundedBoth_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2RepWired.lean)
-/
@[path]
lemma ktypeBoundedness_eq_boundedBoth_iff
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  [AddCommGroup V]
  [Module ℂ V]
  {M : SL2GKModule 𝔤 K 𝔨 Ad V} :
-- imply
  M.ktypeBoundedness = KTypeBoundedness'.boundedBoth ↔ (BddAbove M.ktypeSet ∧ BddBelow M.ktypeSet) := by
-- proof
  classical
  simp only [ktypeBoundedness]
  split_ifs with h1 h2 <;> simp_all

end SL2GKModule

namespace SL2GKModule

/--
[ktypeBoundedness_eq_boundedAbove_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2RepWired.lean)
-/
@[path]
lemma ktypeBoundedness_eq_boundedAbove_iff
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  [AddCommGroup V]
  [Module ℂ V]
  {M : SL2GKModule 𝔤 K 𝔨 Ad V} :
-- imply
  M.ktypeBoundedness = KTypeBoundedness'.boundedAbove ↔ (BddAbove M.ktypeSet ∧ ¬ BddBelow M.ktypeSet) := by
-- proof
  classical
  simp only [ktypeBoundedness]
  split_ifs with h1 h2 <;> simp_all

end SL2GKModule

namespace SL2GKModule

/--
[ktypeBoundedness_eq_boundedBelow_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2RepWired.lean)
-/
@[path]
lemma ktypeBoundedness_eq_boundedBelow_iff
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  [AddCommGroup V]
  [Module ℂ V]
  {M : SL2GKModule 𝔤 K 𝔨 Ad V} :
-- imply
  M.ktypeBoundedness = KTypeBoundedness'.boundedBelow ↔ (¬ BddAbove M.ktypeSet ∧ BddBelow M.ktypeSet) := by
-- proof
  classical
  simp only [ktypeBoundedness]
  split_ifs with h1 h2 <;> simp_all

end SL2GKModule

namespace SL2GKModule

/--
[ktypeBoundedness_eq_unboundedBoth_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2RepWired.lean)
-/
@[path]
lemma ktypeBoundedness_eq_unboundedBoth_iff
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  [AddCommGroup V]
  [Module ℂ V]
  {M : SL2GKModule 𝔤 K 𝔨 Ad V} :
-- imply
  M.ktypeBoundedness = KTypeBoundedness'.unboundedBoth ↔ (¬ BddAbove M.ktypeSet ∧ ¬ BddBelow M.ktypeSet) := by
-- proof
  classical
  simp only [ktypeBoundedness]
  split_ifs with h1 h2 <;> simp_all

end SL2GKModule


-- created on 2026-10-23
