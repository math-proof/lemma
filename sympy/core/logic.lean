import Mathlib.Tactic
import Lemma.Bool.Or.of.Or.Imp
import Lemma.Bool.And.of.And.Imp
import Lemma.Bool.Imp.is.ImpNotS
import Lemma.Bool.Imp.of.Imp.Imp
import stdlib.Lean.Expr -- using Lean.Expr.is_Prop
import stdlib.Lean.FVarId
open Lean Elab.Tactic Meta Parser.Tactic

/--
A helper that returns the correct lemma name for each path step.
-/
def lemmaName : String × Bool → Name
  | ("And", true)  => `Bool.And.of.And.Imp.left
  | ("And", false) => `Bool.And.of.And.Imp
  | ("Or",  true)  => `Bool.Or.of.Or.Imp.left
  | ("Or",  false) => `Bool.Or.of.Or.Imp
  | ("Not",  _) => `Bool.ImpNotS.of.Imp
  | ("Imp",  true) => `Bool.Imp.of.Imp.Imp
  | ("Imp",  false) => `Bool.Imp.of.Imp.Imp.right
  | (_, _)         => panic! "unknown path step"


/--
Build a nested string of the form : apply <lemmaName> (by apply <lemmaName> (by ... apply h₀ ...))
recursively from the front of “path” to the end.
-/
def buildNestedTacticSyntax (path : List (String × Bool)) (h₀ : Term) (h₁ : Option Ident) : TacticM (TSyntax `tactic) :=
  if let step :: rest := path then do
    let lem := mkIdent (lemmaName step)
    if rest == [] then
      -- Base case: apply the final hypothesis
      if let some h₁ := h₁ then
        `(tactic| apply $lem $h₀ at $h₁)
      else
        `(tactic| apply $lem $h₀)
    else
      -- Recursively build the inner tactic
      let inner ← buildNestedTacticSyntax rest h₀ none
      -- Construct the apply tactic with the lemma and the inner tactic
      if let some h₁ := h₁ then
        `(tactic| apply $lem (by { $inner }) at $h₁)
      else
        `(tactic| apply $lem:ident (by { $inner }))
  else
    panic! "buildNestedTacticSyntax: empty path"


/-- Recursive function to find the path to the target proposition in the goal -/
partial def findPath (goal : Expr) (target : Expr) (reverse : Bool) (flip : Bool) : MetaM (Option (List (String × Bool))) := do
  -- logInfo m!"findPath base case, goal = {goal}, target = {target}"
  if (← isDefEq goal target) && reverse == flip then
      return some []

  match goal with
  | .app (.app (.const ``And _) lhs) rhs =>
    -- logInfo m!"findPath And, goal = {goal}\nlhs = {lhs}\nrhs = {rhs}"
    if let some path ← findPath lhs target reverse flip then
      return ⟨"And", true⟩ :: path

    if let some path ← findPath rhs target reverse flip then
      return ⟨"And", false⟩ :: path

  | .app (.app (.const ``Or _) lhs) rhs =>
    -- logInfo m!"findPath Or, goal = {goal}\nlhs = {lhs}\nrhs = {rhs}"
    if let some path ← findPath lhs target reverse flip then
      return ⟨"Or", true⟩ :: path

    if let some path ← findPath rhs target reverse flip then
      return ⟨"Or", false⟩ :: path

  | .app (.const ``Not _) goal =>
    -- logInfo m!"findPath Or, goal = {goal}\nlhs = {lhs}\nrhs = {rhs}"
    if let some path ← findPath goal target reverse !flip then
      return ⟨"Not", false⟩ :: path

  | .forallE _ lhs rhs .default =>
    -- logInfo m!"findPath Or, goal = {goal}\nlhs = {lhs}\nrhs = {rhs}"
    if (← lhs.is_Prop) && (← rhs.is_Prop) then
      if let some path ← findPath lhs target reverse !flip then
        return ⟨"Imp", true⟩ :: path

      if let some path ← findPath rhs target reverse flip then
        return ⟨"Imp", false⟩ :: path

  | .mvar mvarId =>
    -- logInfo m!"findPath mvar, goal = {goal}, target = {target}"
    if let some goal ← Lean.getExprMVarAssignment? mvarId then
      if let some path ← findPath goal target reverse flip then
        return path
  | .mdata _ goal =>
    if let some path ← findPath goal target reverse flip then
      return path
  | _ =>
    -- logInfo m!"base case: goal = {goal}, target = {target}, goal.ctorName = {goal.ctorName}"
    pure ()
  return none


/--
This tactic is used to apply the hypothesis h₀ : p → q to the given proposition:
-/
def applyModusPonens (target : Expr) (h₀ : Term) (prop : Expr) (h₁ : Option Term) (reverse : Bool) : TacticM Unit := do
    findPath prop target reverse false >>= fun path => do
      if let some path := path then
        if let some h₁ := h₁ then
          if let `($h₁:ident) := h₁ then
            evalTactic (← `(tactic| $(← buildNestedTacticSyntax path h₀ h₁)))
          else
            throwError "Expected an identifier for the 'at' modifier, but got {h₁}"
        else
          for step in path do
            evalTactic (← `(tactic| apply $(mkIdent (lemmaName step))))
          evalTactic (← `(tactic| apply $h₀))
      else
        throwError "Could not find the path to target in the prop:\ntarget = {target}\nprop = {prop}"


def performModusPonens (imp : Expr) (h₀ : Term) (h₁ : Option Term) (reverse : Bool) : TacticM Unit := do
  match imp with
  | .forallE _ p q .default =>
    -- logInfo m!"p = {p}"
    unless ← p.is_Prop do
      throwError "p is not a proposition"
    -- logInfo m!"q = {q}"
    unless ← q.is_Prop do
      throwError "q is not a proposition"

    if let some h₁ := h₁ then
      let goal ← inferType (← elabTerm h₁ none)
      if reverse then
        -- p → q, we are going to replace q with p
        -- q must reside in the negation part of the goal
        applyModusPonens q h₀ goal h₁ true
      else
        -- p → q, we are going to replace p with q
        applyModusPonens p h₀ goal h₁ false
    else
      let goal ← getMainTarget
      if reverse then
        -- p → q, we are going to replace q with p
        applyModusPonens q h₀ goal none false
      else
        -- p → q, we are going to replace p with q
        -- p must reside in the negation part of the goal
        applyModusPonens p h₀ goal none true
  | _ =>
    logInfo m!"given hypothesis {imp} is not an implication, with the type of {imp.ctorName}."


def evalModusPonens (h₀ : Array Term) (h₁ : Option Term) (reverse : Bool) : TacticM Unit := do
  for h₀ in h₀ do
    let hExpr ← elabTerm h₀ none
    match hExpr with
    | .fvar fvarId =>
      if let some decl ← fvarId.findDecl? then
        performModusPonens decl.type h₀ h₁ reverse
      else
        logInfo m!"could not find free variable declaration for {fvarId.name}"
    | .app .. =>
      performModusPonens (← inferType hExpr) h₀ h₁ reverse
    | _ =>
      performModusPonens hExpr h₀ h₁ reverse


def employModusPonens (tacticName: Name) (h₀ : Array (TSyntax `term)) (loc : Option (TSyntax `Lean.Parser.Tactic.location)) (reverse : Bool) : TacticM Unit := do
  withLocation (expandOptLocation (mkOptionalNode loc))
    fun fvarId => do (evalModusPonens h₀ (← fvarId.toTerm) reverse)
    (evalModusPonens h₀ none reverse)
    (throwTacticEx tacticName · "did not find instance of the pattern in the current goal")


/--
`mp` tactic tries to employ modus ponens reverse using the given hypothesis.
The hypothesis must be of the form `h₀ : p → q`
- if modifier h₁ is present, h₁ must contain `p`, The tactic replaces `p` in the goal with `q` by applying `h`.
- if modifier h₁ isn't present, the goal must contain `p` which must reside in the negation part. The tactic replaces `p` in the goal with `q`
-/
syntax (name := mp) "mp" "[" term,+ "]" (location)? : tactic

@[tactic mp]
def evalMp : Tactic
| `(tactic| mp [ $[ $h₀ ],* ] $[$loc:location]?) => employModusPonens `mp h₀ loc false
| _ => throwError "Usage: mp [ <term>,+ ] at <location>?"


/--
`mpr` tactic tries to employ modus ponens reverse using the given hypothesis.
The hypothesis must be of the form `h₀ : p → q`
- if modifier h₁ is present, h₁ must contain `q` which resides in the negation part, The tactic replaces `q` with `p` at the local hypothesis h₁
- if modifier h₁ isn't present, the goal must contain `q`. The tactic replaces `q` in the goal with `p`
-/
syntax (name := mpr) "mpr" "[" term,+ "]" (location)? : tactic

@[tactic mpr]
def evalMpr : Tactic
| `(tactic| mpr [ $[ $h₀ ],* ] $[$loc:location]?) => employModusPonens `mpr h₀ loc true
| _ => throwError "Usage: mpr [ <term>,+ ] at <location>?"


def Eq.left {a b : α} (_ : a = b) : α := a
def Eq.right {a b : α} (_ : a = b) : α := b


def evalLet (t : Ident) (e : Expr) : TacticM Unit := do
  let e ← PrettyPrinter.delab e
  evalTactic (← `(tactic| let $t := $e))

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
  evalLet t e
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
  withMainContext do
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
