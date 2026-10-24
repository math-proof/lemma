import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.ParabolicDefs
open BNPair


namespace Definitions
end Definitions
/--
[exists_mem_bruhatCell](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/ParabolicDefs.lean)
-/
@[path]
private lemma exists_mem_bruhatCell_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {w : M.Group} :
-- imply
  (bp.bruhatCell w).Nonempty := by
-- proof
  apply BNPair.exists_mem_bruhatCell bp w

/--
[mem_conj_image_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/ParabolicDefs.lean)
-/
@[path]
private lemma mem_conj_image_self_eq
  [Group G]
  {P : Set G}
  {g : G}
-- given
  (h : g ∈ (fun x => g * x * g⁻¹) '' P) :
-- imply
  g ∈ P := by
-- proof
  apply BNPair.mem_conj_image_self P g h

/--
[conj_image_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/ParabolicDefs.lean)
-/
@[path]
private lemma conj_image_eq_eq
  [Group G]
  {P Q : Set G}
  {g : G}
-- given
  (hgQ : g ∈ Q)
  (hP_mul : ∀ x y, x ∈ P → y ∈ P → x * y ∈ P)
  (hP_inv : ∀ x, x ∈ P → x⁻¹ ∈ P)
  (hconj : (fun x => g * x * g⁻¹) '' P = Q) :
-- imply
  P = Q := by
-- proof
  apply BNPair.conj_image_eq P Q g hgQ hP_mul hP_inv hconj

/--
[standardParabolicInjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/ParabolicDefs.lean)
-/
@[path]
private lemma standardParabolicInjective_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {S₁ S₂ : Set B_idx}
-- given
  (h : bp.standardParabolic S₁ = bp.standardParabolic S₂) :
-- imply
  S₁ = S₂ := by
-- proof
  apply BNPair.standardParabolicInjective bp bd S₁ S₂ h

/--
[parabolicsAreSubgroups](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/ParabolicDefs.lean)
-/
@[path]
private lemma parabolicsAreSubgroups_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {bd : BruhatProperties bp}
  {S' : Set B_idx} :
-- imply
  (1 : G) ∈ bp.standardParabolic S' ∧ (∀ x y, x ∈ bp.standardParabolic S' → y ∈ bp.standardParabolic S' → x * y ∈ bp.standardParabolic S') ∧ (∀ x, x ∈ bp.standardParabolic S' → x⁻¹ ∈ bp.standardParabolic S') := by
-- proof
  apply BNPair.parabolicsAreSubgroups bp bd S'


-- created on 2026-10-24
