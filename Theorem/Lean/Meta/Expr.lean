import Def.Lean.Name
import Def.Lean.BinderInfo.Part2
import Def.Lean.Meta.Expr.Part3
open Lean.Meta
open Lean (BinderInfo PPContext FormatWithInfos Expr Core.Context getEnv getMCtx getLCtx getOptions ppExt)


@[symm]
theorem LT.symm [LT α] {a b : α} (h : a < b) : b > a := h

@[symm]
theorem LE.symm [LE α] {a b : α} (h : a ≤ b) : b ≥ a := h

@[symm]
theorem GT.symm [LT α] {a b : α} (h : a > b) : b < a := h

@[symm]
theorem GE.symm [LE α] {a b : α} (h : a ≥ b) : b ≤ a := h

theorem Not.LT.symm [LT α] {a b : α} (h : ¬a < b) : ¬b > a := h

theorem Not.LE.symm [LE α] {a b : α} (h : ¬a ≤ b) : ¬b ≥ a := h

theorem Not.GT.symm [LT α] {a b : α} (h : ¬a > b) : ¬b < a := h

theorem Not.GE.symm [LE α] {a b : α} (h : ¬a ≥ b) : ¬b ≤ a := h

theorem Not.Iff.symm {a b : Prop} (h : ¬(a ↔ b)) : ¬(b ↔ a) := fun h' => h h'.symm

theorem Not.And.symm {a b : Prop} (h : ¬(a ∧ b)) : ¬(b ∧ a) := fun h' => h h'.symm

theorem Not.Or.symm {a b : Prop} (h : ¬(a ∨ b)) : ¬(b ∨ a) := fun h' => h h'.symm

