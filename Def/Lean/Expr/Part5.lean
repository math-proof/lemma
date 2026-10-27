import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Structure.Lean.Expr.Part4
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


def Special.func : Special → Func
  | ⟨name⟩ =>
    match name with
    | .anonymous => ⟨75, "__call__", "__call__"⟩
    | `abs => ⟨72, "|%s|", "\\left|%s\\right|"⟩  -- LeanAbs
    | `Bool.toNat => ⟨72, "Bool.toNat %s", "\\left|%s\\right|"⟩  -- LeanAbs
    | `Finset.card => ⟨72, "#%s", "\\left|%s\\right|"⟩  -- LeanCard
    | `Norm.norm => ⟨60, "‖%s‖", "\\left\\lVert%s\\right\\rVert"⟩  -- LeanNorm
    | `Int.ceil => ⟨72, "⌈%s⌉", "\\left\\lceil%s\\right\\rceil"⟩  -- LeanCeil
    | `Int.floor => ⟨72, "⌊%s⌋", "\\left\\lfloor%s\\right\\rfloor"⟩  -- LeanFloor
    | `ite => ⟨60, "ite", "ite"⟩  -- LeanITE
    | `dite => ⟨60, "ite", "ite"⟩  -- LeanITE
    | `List.get
    | `List.Vector.get
    | `Tensor.get
    | `GetElem.getElem => ⟨99, "%s[%s]", "%s_%s"⟩  -- LeanGetElem
    | `GetElem?.getElem? => ⟨99, "%s[%s]?", "%s_{%s?}"⟩  -- LeanGetElemQue
    | `Nat.ModEq => ⟨32, "%s ≡ %s [MOD %s]", "%s \\equiv %s\\ \\left[\\text{MOD}\\ %s\\right]"⟩  -- Lean_equiv
    | `Singleton.singleton
    | `Insert.insert => ⟨72, "{%s}", "\\left\\{%s\\right\\}"⟩  -- LeanBrace
    | `setOf => ⟨72, "{%s | %s}", "\\left\\{%s \\mid %s\\right\\}"⟩  -- LeanSetOf
    | `Decidable.decide => ⟨72, "%s", "%s"⟩  -- LeanDecide
    | `OfNat.ofNat => ⟨107, "%s", "\\mathbf{%s}_{%s}"⟩
    | .str _ op  =>
      if op.endsWithNumberedWord "match" then
        ⟨60, "match", "match"⟩  -- Lean_match
      else if op == "mk" then
        ⟨117, "⟨%s, %s⟩", "\\langle %s, %s \\rangle"⟩  -- LeanAngleBracket
      else
        panic! s!"Special.func : unknown operator {name}"
    | _ => panic! s!"Special.func : unknown operator {name}"


