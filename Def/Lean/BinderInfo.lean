module

public meta import Def.Lean.Meta.CtorName
public import Class.Lean.Meta.CtorName
public import Lean

@[expose] public section


def Lean.BinderInfo.pairedGroup : BinderInfo → String × String
  | .default =>
    ⟨"(", ")"⟩
  | .implicit =>
    ⟨"{", "}"⟩
  | .strictImplicit =>
    ⟨"⦃", "⦄"⟩
  | .instImplicit =>
    ⟨"[", "]"⟩


#eval mkCtorName ``Lean.BinderInfo
