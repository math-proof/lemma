import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory


/--
[Theorem_1_22_11](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_22_11.lean)
-/
@[path]
lemma Theorem_1_22_11
  {k : Type w}
  [Field k] :
-- imply
  (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C] [Linear k C] [RigidCategory C] (F : C ⥤ ModuleCat.{w} k) (hFaithful : F.Faithful) (hMono : F.PreservesMonomorphisms) (hEpi : F.PreservesEpimorphisms) (hMonoidal : F.Monoidal), Nonempty (FiniteTannakaHopfData k C)) ∧ (∀ (H : Type w) [Ring H] [Algebra k H] [HopfAlgebra k H] [FiniteDimensional k H], Nonempty (HopfAlgebraRepData k H)) ∧ (∀ (H : Type w) [Ring H] [Algebra k H] [HopfAlgebra k H] [FiniteDimensional k H] (repData : HopfAlgebraRepData k H) [instLinear : Linear k repData.RepH] (reconData : FiniteTannakaHopfData (C := repData.RepH) k), Nonempty (BialgebraEquiv k reconData.H H)) :=
-- proof
  thm_1_22_11 k

/--
[theorem_1_22_11](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_22_11.lean)
-/
@[path]
lemma theorem_1_22_11
  {k : Type w}
  [Field k] :
-- imply
  (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C] [Linear k C] [RigidCategory C] (F : C ⥤ ModuleCat.{w} k) (hFaithful : F.Faithful) (hMono : F.PreservesMonomorphisms) (hEpi : F.PreservesEpimorphisms) (hMonoidal : F.Monoidal), Nonempty (FiniteTannakaHopfData k C)) ∧ (∀ (H : Type w) [Ring H] [Algebra k H] [HopfAlgebra k H] [FiniteDimensional k H], Nonempty (HopfAlgebraRepData k H)) ∧ (∀ (H : Type w) [Ring H] [Algebra k H] [HopfAlgebra k H] [FiniteDimensional k H] (repData : HopfAlgebraRepData k H) [instLinear : Linear k repData.RepH] (reconData : FiniteTannakaHopfData (C := repData.RepH) k), Nonempty (BialgebraEquiv k reconData.H H)) :=
-- proof
  thm_1_22_11 k


-- created on 2026-10-23
