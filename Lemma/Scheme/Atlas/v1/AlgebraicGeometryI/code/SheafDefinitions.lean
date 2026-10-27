import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SheafDefinitions.Part2
open SheafDefinitions
open CategoryTheory TopologicalSpace


namespace SheafDefinitions

/--
[free_isLocallyFree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafDefinitions.lean)
-/
@[path]
lemma free_isLocallyFree
  [TopologicalSpace X]
  {O : (Opens X)ᵒᵖ ⥤ CommRingCat}
  [∀ U, AddCommGroup (M U)]
  [∀ U, Module (O.obj (Opposite.op U)) (M U)]
  {n : ℕ}
  [hfree : Module.Free (O.obj (Opposite.op ⊤)) (M ⊤)]
-- given
  (M : ∀ (U : Opens X), Type*)
  (hrank : Module.finrank (O.obj (Opposite.op ⊤)) (M ⊤) = n) :
-- imply
  IsLocallyFree O M n := by
-- proof
  refine ⟨PUnit, fun _ => ⊤, ?_, ?_⟩
  · simp
  · intro i
    exact ⟨hfree, hrank⟩

end SheafDefinitions


-- created on 2026-10-23
