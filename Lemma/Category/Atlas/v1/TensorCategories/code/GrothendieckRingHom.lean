import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing


namespace FusionRing

/--
[Proposition_1_16_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRingHom.lean)
-/
@[path]
lemma Proposition_1_16_2
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq κ]
  [Fintype κ]
  {R : FusionRing ι}
  {S : FusionRing κ}
  {φ : FusionRingHom R S} :
-- imply
  ∃ f : GrRingOf R →+* GrRingOf S, ∀ a, (f a).coeff = φ.grMap a.coeff :=
-- proof
  ⟨φ.inducedRingHom, fun _ => rfl⟩

end FusionRing


-- created on 2026-10-23
