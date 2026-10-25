import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.Proposition_1_36_5
open CategoryTheory TensorCategories


/--
[cocycleH2ToFiberFunctorClass_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_5.lean)
-/
@[path]
lemma cocycleH2ToFiberFunctorClass_mk
  {k : Type u}
  [Field k]
  {G : Type u}
  [Group G]
  {J : Cocycle2 G kˣ} :
-- imply
  cocycleH2ToFiberFunctorClass k G (@Quotient.mk _ (cocycleCohomologousSetoid G kˣ) J) = @Quotient.mk _ (monoidalFiberFunctorSetoid k (VecG k G)) (cocycleToFiberFunctor k G J) :=
-- proof
  rfl

/--
[cocycleH2ToFiberFunctorClass_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_5.lean)
-/
@[path]
lemma cocycleH2ToFiberFunctorClass_injective
  {k : Type u}
  [Field k]
  {G : Type u}
  [Group G] :
-- imply
  Function.Injective (cocycleH2ToFiberFunctorClass k G) := by
-- proof
  intro q₁ q₂ h
  obtain ⟨J₁, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨J₂, rfl⟩ := Quotient.exists_rep q₂
  apply Quotient.sound
  rw [cocycleH2ToFiberFunctorClass_mk, cocycleH2ToFiberFunctorClass_mk] at h
  exact (cocycleToFiberFunctor_iso_iff_cohomologous k G J₁ J₂).mp (Quotient.exact h)

/--
[cocycleH2ToFiberFunctorClass_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_5.lean)
-/
@[path]
lemma cocycleH2ToFiberFunctorClass_surjective
  {k : Type u}
  [Field k]
  {G : Type u}
  [Group G] :
-- imply
  Function.Surjective (cocycleH2ToFiberFunctorClass k G) := by
-- proof
  intro q
  obtain ⟨FF, rfl⟩ := Quotient.exists_rep q
  obtain ⟨J, hJ⟩ := cocycleToFiberFunctor_surj k G FF
  exact ⟨@Quotient.mk _ (cocycleCohomologousSetoid G kˣ) J,
    by rw [cocycleH2ToFiberFunctorClass_mk]
      exact Quotient.sound ((monoidalFiberFunctorSetoid k (VecG k G)).iseqv.symm hJ)⟩

/--
[cocycleH2ToFiberFunctorClass_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_5.lean)
-/
@[path]
lemma cocycleH2ToFiberFunctorClass_bijective
  {k : Type u}
  [Field k]
  {G : Type u}
  [Group G] :
-- imply
  Function.Bijective (cocycleH2ToFiberFunctorClass k G) :=
-- proof
  ⟨cocycleH2ToFiberFunctorClass_injective k G,
    cocycleH2ToFiberFunctorClass_surjective k G⟩

/--
[Proposition_1_36_5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_5.lean)
-/
@[path]
lemma Proposition_1_36_5
  {k : Type u}
  [Field k]
  {G : Type u}
  [Group G] :
-- imply
  Nonempty (MonoidalFiberFunctorIsoClasses k (VecG k G) ≃ CocycleH2 G kˣ) :=
-- proof
  ⟨(Equiv.ofBijective _ (cocycleH2ToFiberFunctorClass_bijective k G)).symm⟩


-- created on 2026-10-23
