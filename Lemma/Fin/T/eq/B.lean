import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.BNPair.FromBuilding.Part4
open Building Building.GroupAction BNPairFromBuildingData


/--
[T_eq_inf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/FromBuilding.lean)
-/
@[path]
private lemma main
  [DecidableEq V]
  [DecidableEq V] :
-- imply
  data.T = data.B ⊓ data.N :=
-- proof
  rfl



variable [DecidableEq V]
variable [DecidableEq V] [Group G] {b : Building V} {ct : Building.CoxeterTypeOfBuilding b} (data : BNPairFromBuildingData G b ct)
/--
[πFun_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/FromBuilding.lean)
-/
$\varphi$ under the $N$-action on the chambers of $A_0$. -/
private lemma πFun_mul (n₁ n₂ : data.N) :
  data.πFun (n₁ * n₂) = data.πFun n₁ * data.πFun n₂ := by
  simp only [πFun]
  have hmul : data.act.smulFace ((n₁ : G) * (n₂ : G)) data.C₀ =
    data.act.smulFace (n₁ : G) (data.act.smulFace (n₂ : G) data.C₀) :=
    data.act.smulFace_mul _ _ _
  rw [show ((n₁ * n₂ : data.N) : G) = (n₁ : G) * (n₂ : G) from rfl]
  rw [hmul]
  have hn₂ : data.act.smulFaces (n₂ : G) data.A₀.faces = data.A₀.faces := n₂.2
  have hmax₂ : data.A₀.IsMaximal (data.act.smulFace (n₂ : G) data.C₀) :=
    data.smul_preserves_apt_max _ hn₂ _ data.hC₀_max_A₀
  exact data.φ_equivariant (n₁ : G) n₁.2 _ hmax₂


/--
[smulFace_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/FromBuilding.lean)
-/
private lemma smulFace_mul_eq
  [DecidableEq V]
  [Group G]
  {b : Building V}
  {act : GroupAction G b}
  {g₁ g₂ : G}
  {s : Finset V} :
-- imply
  act.smulFace (g₁ * g₂) s = act.smulFace g₁ (act.smulFace g₂ s) := by
-- proof
  apply Building.GroupAction.smulFace_mul act g₁ g₂ s

/--
[smulFace_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/FromBuilding.lean)
-/
private lemma smulFace_one_eq
  [DecidableEq V]
  [Group G]
  {b : Building V}
  {act : GroupAction G b}
  {s : Finset V} :
-- imply
  act.smulFace 1 s = s := by
-- proof
  apply Building.GroupAction.smulFace_one act s

/--
[smulFaces_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/FromBuilding.lean)
-/
private lemma smulFaces_mul_eq
  [DecidableEq V]
  [Group G]
  {b : Building V}
  {act : GroupAction G b}
  {g₁ g₂ : G}
  {F : Set (Finset V)} :
-- imply
  act.smulFaces (g₁ * g₂) F = act.smulFaces g₁ (act.smulFaces g₂ F) := by
-- proof
  apply Building.GroupAction.smulFaces_mul act g₁ g₂ F

/--
[smulFaces_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/FromBuilding.lean)
-/
private lemma smulFaces_one_eq
  [DecidableEq V]
  [Group G]
  {b : Building V}
  {act : GroupAction G b}
  {F : Set (Finset V)} :
-- imply
  act.smulFaces 1 F = F := by
-- proof
  apply Building.GroupAction.smulFaces_one act F

/--
[generates](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/FromBuilding.lean)
-/
private lemma generates_eq
  [DecidableEq V]
  [DecidableEq V] :
-- imply
  Subgroup.closure ((data.B : Set G) ∪ (data.N : Set G)) = ⊤ := by
-- proof
  apply BNPairFromBuildingData.generates


-- created on 2026-10-23
-- updated on 2026-10-24
