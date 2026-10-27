import Mathlib.Tactic
import Def.Lean.Syntax
import Def.Lean.Environment
import Def.Lean.Meta.Expr.Part4
import Def.Lean.ConstantInfo.Part5
open Lean
open Lean.Meta


/--
Helper functions for parsing and transforming declaration names based on infix operators. example:
["Expr", "eq", "Expr", "Expr", "Expr", "lt", "Expr"].parseInfixSegments = [["Expr", "eq", "Expr"], ["Expr"], ["Expr", "lt", "Expr"]]
-/
def List.parseInfixSegments (list : List String) : List (List String) :=
  match _: list with
  | [] => []
  | [x] => [[x]]
  | x :: op :: y =>
    match op with
    | "eq" | "is" | "as" | "ne" | "lt" | "le" | "gt" | "ge" | "in" | "ou" | "et" =>
      list.take 3 :: parseInfixSegments (y.drop 1)
    | _ =>
      [x] :: parseInfixSegments (op :: y)
termination_by list.length

def List.transformPrefix (list : List String) : List String :=
  if list.length == 1 then
    [list.head!.transformPrefix]
  else
    match list[1]! with
    | "eq" | "is" | "as" | "ne" =>
      list.reverse
    | _ =>
      list

def List.decomposeOf (list : List String) (parity : List Bool) (fn : List String → Bool → List String) (offset : ℕ := 0) : List String :=
  if let some i := list.idxOf? "of" then
    let ⟨first, ofPart⟩ := list.splitAt i
    let ofPart :=
      if offset == 0 then
        let segments := ofPart.tail.parseInfixSegments
        let ⟨transformed, rest⟩ := segments.splitAt parity.length
        let transformed := transformed.zip parity |>.map fun ⟨s, b⟩ => if b then s.transformPrefix else s
        ofPart[0]! :: (transformed ++ rest).flatten
      else
        ofPart.drop offset
    first.head! :: fn first.tail true ++ ofPart
  else
    list.head! :: fn list.tail false

def List.commutateIs (list : List String) (op : String := "is") : List String :=
  if let some i := list.idxOf? "is" then
    let ⟨first, second⟩ := list.splitAt i
    second.tail ++ op :: first
  else
    []

def List.comm (list : List String) (parity : List Bool) : List String :=
  list.decomposeOf parity fun list ofPart =>
    let list' := list.commutateIs
    if list'.isEmpty then
      if let first :: rest := list then
        if let op :: second :: rest := rest then
          match op with
          | "eq" | "as" | "ne" | "le" | "ge" | "lt" | "gt" | "ou" =>
            [second, op, first] ++ rest
          | _ =>
            panic! s!"Expected the operator 'eq', 'as or 'ne', got: {op}"
        else
          let first' := first.transformPrefix
          if first' == first then
            if ofPart then list else list ++ ["comm"]
          else
            first' :: rest
      else
        panic! s!"Declaration does not have the form `... eq/is/as/ne ...`, got: {list}"
    else
      list'

def List.zipParity (binders : List (Name × Expr × BinderInfo)) (parity : ℕ) (info : BinderInfo := .default) : List (Bool × Name × Expr × BinderInfo) :=
  binders.foldr
    (fun binder@⟨_, _, binderInfo⟩ ⟨binders, parity⟩ =>
      let ⟨bit, parity⟩ :=
        if binderInfo == info then
          (parity % 2 == 1, parity / 2)
        else
          (false, parity)
      ⟨⟨bit, binder⟩ :: binders, parity⟩
    )
    ([], parity)
  |> Prod.fst

def List.extractParity (parity : List (Bool × Expr)) : CoreM (List String × List Bool) := do
  let moduleTokens := (← getEnv).moduleTokens
  let i := moduleTokens.idxOf "of"
  let ofPart := (moduleTokens.splitAt i).snd.tail
  let parity ←
    if parity.length > ofPart.length && ofPart.length > 0 then
      parity.filterMapM fun ⟨comm, type⟩ => do
        try
          if ← MetaM.run' type.is_Prop then
            return some comm
          else
            return none
        catch _ =>
          return none
    else
      pure (parity.map fun ⟨comm, _⟩ => comm)
  return ⟨moduleTokens, parity⟩

def Expr.comm (type value : Expr) (parity : ℕ := 0) : List (Bool × Expr) × Expr × Expr :=
  let ⟨binders, type⟩ := type.decompose_forallE
  let binders := binders.zipParity parity
  let ⟨type, symm⟩ := type.decompose (fun _ => .comm) .symm
  let telescope := fun localBinders lam body =>
    binders.foldl
      (fun body ⟨comm, binderName, binderType, binderInfo⟩ => lam binderName (if comm then binderType.comm else binderType) body binderInfo)
      (localBinders.foldl
        (fun body ⟨declName, type, deBruijn⟩ =>
          let type := type.incDeBruijnIndex (deBruijn + 1)
          .letE declName type (.app type.comm.symm (.bvar deBruijn)) ((body.incDeBruijnIndex 1).setDeBruijnIndex (deBruijn + 1) 0) false
        )
        body
      )
  let valueBinders := binders.zipIdx.filterMap fun ⟨⟨comm, binderName, binderType, _⟩, deBruijn⟩ => if comm then some (binderName, binderType, deBruijn) else none
  (
    binders.filterMap fun ⟨comm, _, binderType, binderInfo⟩ => if binderInfo == .default then some ⟨comm, binderType⟩ else none,
    (type, .app symm (value.mkApp ((List.range binders.length).map fun i => .bvar i).reverse)).map
      (telescope (valueBinders.filterMap fun args@⟨_, _, deBruijn⟩ => if type.containsBVar deBruijn then some args else none) Expr.forallE)
      (telescope valueBinders .lam)
  )


