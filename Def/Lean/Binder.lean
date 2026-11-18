module

public import Class.Lean.Meta.CtorName
public import Inductive.Lean.Binder

@[expose] public section


def Binder.toString : Binder → String := CtorName.ctorName
