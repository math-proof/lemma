import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.NumberTheory.Ramanujan.Part1Ch1Entry1
open MathlibExt.NumberTheory.Ramanujan.Part1Ch1.Entry1Magicsquare3


namespace MathlibExtTest.NumberTheory.Ramanujan.Part1Ch1Entry1

/--
[bijective_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Ramanujan/Part1Ch1Entry1.lean)
-/
@[path]
private lemma bijective_fin1 (f : Fin 1 → Fin 1) : Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end MathlibExtTest.NumberTheory.Ramanujan.Part1Ch1Entry1

namespace MathlibExtTest.NumberTheory.Ramanujan.Part1Ch1Entry1

/--
[bijective_fin1_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Ramanujan/Part1Ch1Entry1.lean)
-/
@[path]
private lemma bijective_fin1_prod (f : Fin 1 × Fin 1 → Fin 1 × Fin 1) :
  Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun _ => ⟨(0, 0), Subsingleton.elim _ _⟩⟩

end MathlibExtTest.NumberTheory.Ramanujan.Part1Ch1Entry1


-- created on 2026-10-23
