module

public import Class.Lean.Meta.CtorName
public import Inductive.Lean.Meta.Expr

@[expose] public section


def Binder.toString : Binder → String := CtorName.ctorName
