import Lean
open Lean Elab Tactic Meta


def Eq.left {a b : α} (_ : a = b) : α := a
def Eq.right {a b : α} (_ : a = b) : α := b


def evalHave (h_t : Ident) (t : Ident) (e : Expr) (reverse : Bool) : TacticM Unit := do
  let e ← PrettyPrinter.delab e
  let eq ← if reverse then `($e = $t) else `($t = $e)
  evalTactic (← `(tactic| have $h_t : $eq := rfl))


def letAssignment (h_t : Ident) (t : Ident) (reverse : Bool) : TacticM Unit := do
  let mainGoal ← getMainGoal
  let (fvarId, mainGoal) ← mainGoal.intro t.getId
  replaceMainGoal [mainGoal]
  mainGoal.withContext do
    let some decl ← fvarId.findDecl? | throwError "denote: failed to find the declaration from `let statement "
    let some e := decl.value? | throwError "denote: failed to find the value from the `let statement"
    evalHave h_t t e reverse


def haveDeclaration (h_t : Ident) (t : Ident) (e : Expr) (reverse : Bool) : TacticM Unit := do
  let e :=
    match e with
    | .app (.app (.app (.app (.const ``Eq.right _) _) _) rhs) _ => rhs
    | .app (.app (.app (.app (.const ``Eq.left _) _) lhs) _) _ => lhs
    | e => e
  let mainGoal ← getMainGoal
  let mainGoal ← mainGoal.define t.getId (← inferType e) e
  let (_, mainGoal) ← mainGoal.intro t.getId
  replaceMainGoal [mainGoal]
  evalHave h_t t e reverse


/--
Syntax for `denote` tactic:
- extract the left hand side of the given hypothesis h
  - denote h_t : t = h.left
  - denote h_t : h.left = t

- extract the right hand side of the given hypothesis h
  - denote h_t : t = h.right
  - denote h_t : h.right = t

- extract the left hand side of the main goal
  - denote h_t : t = left
  - denote h_t : left = t

- extract the right hand side of the main goal
  - denote h_t : t = right
  - denote h_t : right = t

- extract the left `let-binding` (which is the `let expression`) of the main goal
  - denote h_t : t = _
  - denote h_t : _ = t

wherein:
* h   is the name of an existing hypothesis h : A = B (an equality)
* t   is the new name for the right‐hand side of h
* h_t is the name for the new hypothesis t = h.right
-/
syntax (name := denote) "denote" ident ":" term:51 "=" term : tactic

@[tactic denote]
def evalDenote : Tactic
| `(tactic| denote $h_t : $lhs = $rhs) => do
  match lhs.raw with
  | .ident _ _ val _ =>
    match val with
    | `left =>
      haveDeclaration h_t ⟨rhs.raw⟩ (← Conv.getLhs) true
    | `right =>
      haveDeclaration h_t ⟨rhs.raw⟩ (← Conv.getRhs) true
    | _ =>
      match rhs.raw with
      | .ident _ _ val _ =>
        let e ←
          match val with
          | `left => Conv.getLhs
          | `right => Conv.getRhs
          | _ => elabTermForApply rhs
        haveDeclaration h_t ⟨lhs.raw⟩ e false
      | .node _ `Lean.Parser.Term.hole #[.atom _ "_"] =>
        letAssignment h_t ⟨lhs.raw⟩ false
      | .node .. =>
        haveDeclaration h_t ⟨lhs.raw⟩ (← elabTermForApply rhs) false
      | _ =>
        throwError "denote: invalid syntax, rhs `{rhs}` must be one of left, right, _ or term"
  | .node _ `Lean.Parser.Term.hole #[.atom _ "_"] =>
    letAssignment h_t ⟨rhs.raw⟩ true
  | .node _ _ _ =>
    haveDeclaration h_t ⟨rhs.raw⟩ (← elabTermForApply lhs) true
  | _ =>
    throwError "denote: invalid syntax, lhs `{lhs}` must be one of left, right, _ or term"
| stx => do
  throwError "invalid syntax: {stx}"
