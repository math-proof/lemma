module
public import Theorem.GroupTheory.DicksonPGL2Wild.Part6
public import Theorem.Fin.Card.eq.MulCardSubSquareCard1


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/DicksonPGL2Wild.lean -/
namespace MathlibExtTest.GroupTheory.DicksonPGL2Wild

open MetaMathlibExt.Dickson

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

instance : Fact (2 < 3) := ⟨by decide⟩

end MathlibExtTest.GroupTheory.DicksonPGL2Wild
