/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/MorphicWord.lean -/
module

public import Def.Combinatorics.InfiniteWord.MorphicWord
public import Theorem.Finset.InfiniteWord.MorphicWord

public section

namespace MetaMathlibExt

example {A : Type*} [Finite A] {w : Nat → A} (h : IsPureMorphic w) : IsMorphic w id w :=
  IsMorphic.ofPureMorphic h

example {A B : Type*} [Finite A] {u : Nat → A} {coding : A → B} {w : Nat → B}
    (h : IsMorphic u coding w) : IsPureMorphic u ∧ ∀ n, w n = coding (u n) :=
  ⟨h.pure, h.coding_eq⟩

example {A B : Type*} [Finite A] {u : Nat → A} (hpure : IsPureMorphic u) (b : B) :
    IsMorphic u (fun _ => b) (fun _ => b) := by
  exact IsMorphic.intro hpure (fun _ => rfl)

#print axioms IsMorphic
#print axioms IsMorphic.intro
#print axioms IsMorphic.pure
#print axioms IsMorphic.coding_eq
#print axioms IsMorphic.ofPureMorphic

end MetaMathlibExt
