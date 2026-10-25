import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraNotes.code.RepresentationTheory
open RepresentationTheory
open CategoryTheory Module


namespace RepresentationTheory

/--
[maschke_complement](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/RepresentationTheory.lean)
-/
@[path]
lemma maschke_complement
  [Field k]
  [Group G]
  [Finite G]
  [NeZero (Nat.card G : k)]
  [AddCommGroup V]
  [Module (MonoidAlgebra k G) V]
  {p : Submodule (MonoidAlgebra k G) V} :
-- imply
  ∃ q : Submodule (MonoidAlgebra k G) V, IsCompl p q :=
-- proof
  MonoidAlgebra.Submodule.exists_isCompl p

end RepresentationTheory

namespace RepresentationTheory

/--
[maschke_semisimple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/RepresentationTheory.lean)
-/
@[path]
lemma maschke_semisimple
  [Field k]
  [Group G]
  [Finite G]
  [NeZero (Nat.card G : k)]
  [AddCommGroup V]
  [Module k V]
  {ρ : Representation k G V} :
-- imply
  ρ.IsSemisimpleRepresentation :=
-- proof
  inferInstance

end RepresentationTheory

namespace RepresentationTheory

/--
[maschke_semisimple_complex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/RepresentationTheory.lean)
-/
@[path]
lemma maschke_semisimple_complex
  [Group G]
  [Finite G]
  [AddCommGroup V]
  [Module ℂ V]
  {ρ : Representation ℂ G V} :
-- imply
  ρ.IsSemisimpleRepresentation := by
-- proof
  haveI : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  exact maschke_semisimple ρ

end RepresentationTheory


-- created on 2026-10-23
