import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.Matroid.Algebraic.Part4


namespace AlgebraicMatroidTest

/--
[indep_singleton_X](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean)
-/
@[path]
private lemma indep_singleton_X : testMatroidTrans.Indep {RatFunc.X} := by
  unfold testMatroidTrans
  rw [Matroid.comapOn_indep_iff]
  simp only [Set.image_id]
  have hAlg : (AlgebraicIndependent.matroid (ZMod 2) (RatFunc (ZMod 2))).Indep
    {RatFunc.X} := by
    rw [AlgebraicIndependent.matroid_indep_iff]
    unfold AlgebraicIndepOn
    rwa [algebraicIndependent_singleton_iff ⟨RatFunc.X, Set.mem_singleton RatFunc.X⟩]
  have hInj : Set.InjOn (id : RatFunc (ZMod 2) → RatFunc (ZMod 2)) {RatFunc.X} :=
    Set.injOn_id _
  have hSub : ({RatFunc.X} : Set (RatFunc (ZMod 2))) ⊆ Set.univ :=
    Set.subset_univ _
  exact ⟨hAlg, hInj, hSub⟩

end AlgebraicMatroidTest


-- created on 2026-10-23
