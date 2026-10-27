import Initialize.Lean.Meta.CtorName
import Instance.Lean.BinderInfo


def Lean.BinderInfo.pairedGroup : BinderInfo → String × String
  | .default =>
    ⟨"(", ")"⟩
  | .implicit =>
    ⟨"{", "}"⟩
  | .strictImplicit =>
    ⟨"⦃", "⦄"⟩
  | .instImplicit =>
    ⟨"[", "]"⟩

