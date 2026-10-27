import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Structure.Lean.Expr
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


def BinaryInfix.func : BinaryInfix → Func
  | ⟨name⟩ =>
    match name with
    -- relational operator
    | `Iff => ⟨20, "↔", "\\leftrightarrow"⟩  -- Lean_leftrightarrow, https://github.com/leanprover/lean4/blob/v4.23.0/src/Init/Core.lean#L190
    | `Or => ⟨30, "∨", "\\lor"⟩  -- Lean_lor
    | `or => ⟨30, "||", "||"⟩  -- LeanLogicOr
    | `xor => ⟨33, "^^", "\\^\\^"⟩  -- Lean_xor, https://github.com/leanprover/lean4/blob/v4.23.0/src/Init/Data/Bool.lean#L31
    | `And => ⟨35, "∧", "\\land"⟩  -- Lean_land
    | `and => ⟨35, "&&", "&&"⟩  -- LeanLogicAnd
    | `LE.le => ⟨50, "≤", "\\le"⟩  -- Lean_le
    | `GE.ge => ⟨50, "≥", "\\ge"⟩  -- Lean_ge
    | `LT.lt => ⟨50, "<", "<"⟩  -- Lean_lt
    | `GT.gt => ⟨50, ">", ">"⟩  -- Lean_gt
    | `Eq => ⟨50, "=", "="⟩  -- LeanEq
    | `Ne => ⟨50, "≠", "\\ne"⟩ -- Lean_ne
    | `BEq.beq => ⟨50, "==", "=="⟩  -- LeanBEq
    | `bne => ⟨50, "!=", "!="⟩  -- Lean_bne
    | `HEq => ⟨50, "≍", "\\asymp"⟩  -- Lean_asymp
    | `SEq => ⟨50, "≃", "\\simeq"⟩  -- Lean_simeq
    | `Membership.mem
    | `List.Mem => ⟨50, "∈", "\\in"⟩  -- Lean_in ∋ \\ni
    | `HasSubset.Subset => ⟨50, "⊆", "\\subseteq"⟩  -- Lean_subseteq
    | `HasSSubset.SSubset => ⟨50, "⊂", "\\subset"⟩  -- Lean_subset
    | `Superset => ⟨50, "⊇", "\\supseteq"⟩  -- Lean_supseteq
    | `SSuperset => ⟨50, "⊃", "\\supset"⟩    -- Lean_supset
    | `Dvd.dvd => ⟨50, "∣", "{\\color{red}\\ \\mid\\ }"⟩  -- Lean_mid
    | `HasEquiv.Equiv => ⟨50, "≈", "\\approx"⟩
    | `HOr.hOr => ⟨55, "|||", "\\mid\\mid\\mid"⟩  -- LeanBitwiseOr
    | `HXor.hXor => ⟨58, "^^^", "\\^\\^\\^"⟩  -- LeanBitwiseXor
    | `HAnd.hAnd => ⟨60, "&&&", "\\&\\!\\!\\&\\!\\!\\&"⟩  -- LeanBitwiseAnd
    -- arithmetic operator
    | `Nat.add
    | `HAdd.hAdd => ⟨65, "+", "+"⟩ -- LeanAdd
    | `Nat.sub
    | `HSub.hSub => ⟨65, "-", "-"⟩  -- LeanSub
    | `HAppend.hAppend => ⟨65, "++", "+\\!\\!+"⟩ -- LeanAppend
    | `Mul.mul
    | `HMul.hMul => ⟨70, "*", "\\cdot"⟩  -- LeanMul
    | `Div.div
    | `HDiv.hDiv
    | `Rat.divInt => ⟨70, "/", "\\frac"⟩  -- LeanDiv
    | `HMod.hMod => ⟨70, "%%", "\\%%"⟩  -- LeanMod
    | `HShiftLeft.hShiftLeft => ⟨75, "<<<", "\\lll"⟩ -- Lean_lll
    | `HShiftRight.hShiftRight => ⟨75, ">>>", "\\ggg"⟩  -- Lean_ggg
    | `SDiff.sdiff => ⟨70, "\\", "\\setminus"⟩  -- Lean_setminus
    | `Union.union => ⟨65, "∪", "\\cup"⟩  -- Lean_cup
    | `Inter.inter => ⟨70, "∩", "\\cap"⟩  -- Lean_cap
    | `OPlus.oplus => ⟨30, "⊕", "\\oplus"⟩  -- Lean_oplus
    | `OTimes.otimes => ⟨32, "⊗", "\\otimes"⟩  -- Lean_otimes
    | `ODot.odot => ⟨73, "⊙", "\\odot"⟩  -- Lean_odot
    | `Bullet.bullet
    | `HSMul.hSMul => ⟨73, "•", "\\bullet"⟩  -- Lean_bullet
    | `List.cons => ⟨67, "::", "::"⟩  -- LeanConstruct
    | `List.Vector.cons => ⟨67, "::ᵥ", "::_v"⟩  -- LeanVConstruct
    | `Max.max => ⟨68, "⊔", "\\sqcup"⟩  -- Lean_sqcup
    | `Min.min => ⟨69, "⊓", "\\sqcap"⟩  -- Lean_sqcap
    | `Dot.dot
    | `List.Vector.dot => ⟨70, "@", "{\\color{red}\\times}"⟩  -- LeanMatMul
    | `HPow.hPow => ⟨80, "^", "^"⟩  -- LeanPow
    | `Function.comp => ⟨90, "∘", "\\circ"⟩  -- Lean_circ
    | `Prod => ⟨35, "×", "×"⟩  -- Lean_Prod
    | `PProd => ⟨35, "×'", "×'"⟩  -- Lean_Prod
    | `Functor.map => ⟨100, "<$>", "<$>"⟩
    | `Functor.mapRev => ⟨100, "<&>", "<&>"⟩
    | `orM => ⟨30, "<||>", "<||>"⟩
    | `andM => ⟨35, "<&&>", "<&&>"⟩
    | `Bind.bind => ⟨55, ">>=", ">>="⟩
    | `Bind.kleisliRight => ⟨55, ">=>", ">=>"⟩
    | `Bind.kleisliLeft => ⟨55, "<=<", "<=<"⟩
    | `Bind.bindLeft => ⟨55, "=<<", "=<<"⟩
    | `List.IsPrefix => ⟨50, "<+:", "<+:"⟩
    | `List.IsSuffix => ⟨50, "<:+", "<:+"⟩
    | `List.IsInfix => ⟨50, "<:+:", "<:+:"⟩
    | _ => panic! s!"BinaryInfix.func : unknown operator {name}"


def BinaryInfix.isProp : BinaryInfix → Bool
  | ⟨name⟩ =>
    match name with
    | `LE.le
    | `GE.ge
    | `LT.lt
    | `GT.gt
    | `Eq
    | `Ne
    | `HEq
    | `SEq
    | `HasEquiv.Equiv
    | `And
    | `Or
    | `Iff
    | `Membership.mem
    | `List.Mem
    | `HasSubset.Subset
    | `HasSSubset.SSubset
    | `Superset
    | `SSuperset
    | `Dvd.dvd => true
    | _ => false


