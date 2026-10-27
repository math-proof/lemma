import Lean


def Lean.FVarId.toTerm (fvarId : FVarId) : MetaM (TSyntax `term) := do
  let some decl ← fvarId.findDecl? | throwError "FVarId {fvarId.name} not found"
  return ⟨mkIdent decl.userName⟩

