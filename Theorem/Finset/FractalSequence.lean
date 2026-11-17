module

public import Mathlib
public import Structure.Combinatorics.FractalSequence

public section

open MetaMathlibExt


namespace MetaMathlibExt

/--
[FractalSequence.pos_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/FractalSequence.lean)
-/
public theorem FractalSequence.pos_injective
  {X : FractalSequence}
  {i : ℕ} :
-- imply
  Function.Injective (X.pos i) :=
-- proof
  (X.pos_strict i).injective

end MetaMathlibExt

namespace MetaMathlibExt

/--
[FractalSequence.infinite_occurrences](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/FractalSequence.lean)
-/
public theorem FractalSequence.infinite_occurrences
  {X : FractalSequence}
  {i : ℕ} :
-- imply
  Set.Infinite {n | X.seq n = i + 1} := by
-- proof
  have hf : Function.Injective
    (fun j => (⟨X.pos i j, X.pos_sound i j⟩ : {n // X.seq n = i + 1})) := by
    intro a b hab
    have hpos : X.pos i a = X.pos i b := congrArg Subtype.val hab
    exact (X.pos_strict i).injective hpos
  exact Set.infinite_coe_iff.mp (Infinite.of_injective _ hf)

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
