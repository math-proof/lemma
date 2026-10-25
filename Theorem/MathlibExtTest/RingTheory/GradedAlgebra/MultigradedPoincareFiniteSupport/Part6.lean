/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean -/


import Theorem.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
import Lemma.Int.GradedAlgebra.MultigradedPoincareFiniteSupport
import Def.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport.Part4
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

theorem inclInjAux : ∀ (α : Fin n →₀ Int) (i : ℕ),
    Function.Injective ⇑(ModuleCat.Hom.hom ((inclFn α).f i)) := by
  intro α i x y _
  have _hs := compTermSubsingleton α i
  have hx0 : x = 0 := Subsingleton.elim _ _
  have hy0 : y = 0 := Subsingleton.elim _ _
  rw [hx0, hy0]

theorem rangeEqAux : ∀ (α : Fin n →₀ Int) (i : ℕ),
    LinearMap.range (ModuleCat.Hom.hom ((inclFn α).f i)) =
      MetaMathlibExt.baseChangedDegreePiece targetGraded resolution ι resFree i α := by
  intro α i
  have _hDom := compTermSubsingleton α i
  have _hCod := baseSubsingleton i
  rw [pieceIsBot i α]
  apply le_antisymm
  · rintro y ⟨w, rfl⟩
    have hw0 : w = 0 := Subsingleton.elim _ _
    have hmap0 : ModuleCat.Hom.hom ((inclFn α).f i) 0 = 0 :=
      Subsingleton.elim _ _
    rw [hw0, hmap0]
    exact Submodule.zero_mem _
  · exact bot_le

end MetaMathlibExtTest
end
