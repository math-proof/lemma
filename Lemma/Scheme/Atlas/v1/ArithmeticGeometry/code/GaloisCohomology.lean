import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology
open groupCohomology GaloisCohomology GaloisCohomology.CrossedHom GaloisCohomology.ContCrossedHom
open scoped Classical


namespace GaloisCohomology.CrossedHom

/--
[coe_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
lemma coe_mk
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  {f : G → A}
  (hf) :
-- imply
  (CrossedHom.mk f hf : G → A) = f :=
-- proof
  rfl

end GaloisCohomology.CrossedHom

namespace GaloisCohomology.CrossedHom

/--
[cocycle_condition_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
lemma cocycle_condition_eq
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  {α : CrossedHom G A}
  {τ σ : G} :
-- imply
  α (τ * σ) = α τ + τ • α σ := by
-- proof
  have := α.cocycle_condition τ σ
  rwa [add_comm] at this

end GaloisCohomology.CrossedHom

namespace GaloisCohomology.CrossedHom

/--
[isCrossedHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
lemma isCrossedHom
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  {α : CrossedHom G A} :
-- imply
  IsCrossedHom (α : G → A) :=
-- proof
  α.cocycle_condition

end GaloisCohomology.CrossedHom

namespace GaloisCohomology.ContCrossedHom

/--
[coe_mk'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
lemma coe_mk'
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  {f : CrossedHom G A}
  (hf) :
-- imply
  (ContCrossedHom.mk f hf : G → A) = f :=
-- proof
  rfl

end GaloisCohomology.ContCrossedHom

namespace GaloisCohomology.ContCrossedHom

/--
[cocycle_condition_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
lemma cocycle_condition_eq
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  {α : ContCrossedHom G A}
  {τ σ : G} :
-- imply
  α (τ * σ) = α τ + τ • α σ :=
-- proof
  α.toCrossedHom.cocycle_condition_eq τ σ

end GaloisCohomology.ContCrossedHom

namespace GaloisCohomology.ContCrossedHom

/--
[continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
lemma continuous
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  {α : ContCrossedHom G A} :
-- imply
  Continuous α :=
-- proof
  α.continuous_toFun

end GaloisCohomology.ContCrossedHom

namespace GaloisCohomology.ContCrossedHom

/--
[isCrossedHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
lemma isCrossedHom
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  {α : ContCrossedHom G A} :
-- imply
  IsCrossedHom (α : G → A) :=
-- proof
  α.toCrossedHom.cocycle_condition

end GaloisCohomology.ContCrossedHom

namespace GaloisCohomology.ContCrossedHom

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A] [TopologicalSpace G] [TopologicalSpace A]
/--
[isCocycle₁](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
lemma isCocycle₁ (α : ContCrossedHom G A) : groupCohomology.IsCocycle₁ (α : G → A) :=
  α.toCrossedHom.cocycle_condition
section Group
variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
  [TopologicalSpace G] [TopologicalSpace A] [ContinuousAdd A] [ContinuousNeg A]

end GaloisCohomology.ContCrossedHom

namespace GaloisCohomology

/--
[isPrincipalCrossedHom_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
lemma isPrincipalCrossedHom_iff
  [Group G]
  [AddCommGroup A]
  [DistribMulAction G A]
  {α : G → A} :
-- imply
  IsPrincipalCrossedHom α ↔ ∃ P : A, ∀ σ : G, σ • P - P = α σ :=
-- proof
  Iff.rfl

end GaloisCohomology

namespace GaloisCohomology

/--
[principalCrossedHom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
lemma principalCrossedHom_apply
  [Group G]
  [AddCommGroup A]
  [DistribMulAction G A]
  {P : A}
  {σ : G} :
-- imply
  principalCrossedHom P σ = σ • P - P :=
-- proof
  rfl

end GaloisCohomology

namespace GaloisCohomology

/--
[mem_principalCrossedHomSubgroup_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
lemma mem_principalCrossedHomSubgroup_iff
  [Group G]
  [AddCommGroup A]
  [DistribMulAction G A]
  {α : CrossedHom G A} :
-- imply
  α ∈ principalCrossedHomSubgroup G A ↔ IsPrincipalCrossedHom (α : G → A) :=
-- proof
  Iff.rfl
section Continuous
variable [TopologicalSpace G] [TopologicalSpace A]
  [ContinuousAdd A] [ContinuousNeg A] [ContinuousSMul G A]

end GaloisCohomology

namespace GaloisCohomology

/--
[contPrincipalCrossedHom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
lemma contPrincipalCrossedHom_apply
  [Group G]
  [AddCommGroup A]
  [DistribMulAction G A]
  [TopologicalSpace G]
  [TopologicalSpace A]
  {P : A}
  {σ : G} :
-- imply
  contPrincipalCrossedHom P σ = σ • P - P :=
-- proof
  rfl

end GaloisCohomology

namespace GaloisCohomology

/--
[mem_contPrincipalCrossedHomSubgroup_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
lemma mem_contPrincipalCrossedHomSubgroup_iff
  [Group G]
  [AddCommGroup A]
  [DistribMulAction G A]
  [TopologicalSpace G]
  [TopologicalSpace A]
  {α : ContCrossedHom G A} :
-- imply
  α ∈ contPrincipalCrossedHomSubgroup G A ↔ IsPrincipalCrossedHom (α : G → A) :=
-- proof
  Iff.rfl
section H1
variable (G A : Type*) [Group G] [AddCommGroup A] [DistribMulAction G A]
  [TopologicalSpace G] [TopologicalSpace A] [ContinuousAdd A] [ContinuousNeg A]
  [ContinuousSMul G A]

end GaloisCohomology

namespace GaloisCohomology

/--
[H1.eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
lemma H1.eq_iff
  {G A : Type*}
  [Group G]
  [AddCommGroup A]
  [DistribMulAction G A]
  {α β : ContCrossedHom G A} :
-- imply
  H1.mk G A α = H1.mk G A β ↔ α - β ∈ contPrincipalCrossedHomSubgroup G A := by
-- proof
  rw [H1.mk, H1.mk, QuotientAddGroup.eq]
  constructor
  · intro h
    have : -(-α + β) = α - β := by abel
    rw [← this]
    exact (contPrincipalCrossedHomSubgroup G A).neg_mem h
  · intro h
    have : -α + β = -(α - β) := by abel
    rw [this]
    exact (contPrincipalCrossedHomSubgroup G A).neg_mem h
section WeilChateletGroupReal
open scoped Classical

end GaloisCohomology

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
private lemma ext_eq
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  {α β : CrossedHom G A}
-- given
  (h : ∀ g, α g = β g) :
-- imply
  α = β := by
-- proof
  apply GaloisCohomology.CrossedHom.ext h

/--
[zero_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
private lemma zero_apply_eq
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  [Group G]
  [AddCommGroup A]
  [DistribMulAction G A]
  {g : G} :
-- imply
  (0 : CrossedHom G A) g = 0 := by
-- proof
  apply GaloisCohomology.CrossedHom.zero_apply g

/--
[add_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
private lemma add_apply_eq
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  [Group G]
  [AddCommGroup A]
  [DistribMulAction G A]
  {α β : CrossedHom G A}
  {g : G} :
-- imply
  (α + β) g = α g + β g := by
-- proof
  apply GaloisCohomology.CrossedHom.add_apply α β g

/--
[neg_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
private lemma neg_apply_eq
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  [Group G]
  [AddCommGroup A]
  [DistribMulAction G A]
  {α : CrossedHom G A}
  {g : G} :
-- imply
  (-α) g = -(α g) := by
-- proof
  apply GaloisCohomology.CrossedHom.neg_apply α g

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
private lemma ext_eq_2
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  {α β : ContCrossedHom G A}
-- given
  (h : ∀ g, α g = β g) :
-- imply
  α = β := by
-- proof
  apply GaloisCohomology.ContCrossedHom.ext h

/--
[isCocycle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
private lemma isCocycle_eq
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  {α : ContCrossedHom G A} :
-- imply
  groupCohomology.IsCocycle₁ (α : G → A) := by
-- proof
  apply GaloisCohomology.ContCrossedHom.isCocycle α

/--
[zero_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
private lemma zero_apply_eq_2
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  [Group G]
  [AddCommGroup A]
  [DistribMulAction G A]
  {g : G} :
-- imply
  (0 : ContCrossedHom G A) g = 0 := by
-- proof
  apply GaloisCohomology.ContCrossedHom.zero_apply g

/--
[add_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
private lemma add_apply_eq_2
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  [Group G]
  [AddCommGroup A]
  [DistribMulAction G A]
  {α β : ContCrossedHom G A}
  {g : G} :
-- imply
  (α + β) g = α g + β g := by
-- proof
  apply GaloisCohomology.ContCrossedHom.add_apply α β g

/--
[neg_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
private lemma neg_apply_eq_2
  [Mul G]
  [AddCommGroup A]
  [SMul G A]
  [Group G]
  [AddCommGroup A]
  [DistribMulAction G A]
  {α : ContCrossedHom G A}
  {g : G} :
-- imply
  (-α) g = -(α g) := by
-- proof
  apply GaloisCohomology.ContCrossedHom.neg_apply α g

/--
[IsPrincipalCrossedHom.isCrossedHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean)
-/
@[path]
private lemma isCrossedHom_eq_3
  [Group G]
  [AddCommGroup A]
  [DistribMulAction G A]
  {α : G → A}
-- given
  (h : IsPrincipalCrossedHom α) :
-- imply
  IsCrossedHom α := by
-- proof
  apply GaloisCohomology.IsPrincipalCrossedHom.isCrossedHom h


-- created on 2026-10-23
