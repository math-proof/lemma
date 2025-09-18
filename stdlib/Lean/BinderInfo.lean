import stdlib.Basic
#eval mkCtorName ``Lean.BinderInfo

instance : ToString Lean.BinderInfo where
  toString := ctorName

def Lean.BinderInfo.pairedGroup : BinderInfo → String × String
  | .default =>
    ⟨"(", ")"⟩
  | .implicit =>
    ⟨"{", "}"⟩
  | .strictImplicit =>
    ⟨"⦃", "⦄"⟩
  | .instImplicit =>
    ⟨"[", "]"⟩
