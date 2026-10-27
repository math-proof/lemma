import Def.Data.String.String.Part2
open Lean


def buildNestedTacticString (lemmaName : String × Bool → Name) (path : List (String × Bool)) (h₀ : Term) (h₁ : Option Ident) (level : Nat := 0) : String :=
  if let step :: rest := path then
    let lem := lemmaName step
    if rest == [] then
      -- Base case: apply the final hypothesis
      if let some h₁ := h₁ then
        let h₁ := h₁.getId.toString
        s!"apply {lem} {h₀} at {h₁}"
      else
        s!"apply {lem} {h₀}"
    else
      let level := level.succ
      -- Recursively build the inner tactic
      let inner := buildNestedTacticString lemmaName rest h₀ none level
      -- Construct the apply tactic with the lemma and the inner tactic
      let lem := lemmaName step
      let indent := "  ".repeat level
      if let some h₁ := h₁ then
        let h₁ := h₁.getId.toString
        s!"apply {lem} (by \n{indent}{inner}) at {h₁}"
      else
        s!"apply {lem} (by \n{indent}{inner})"
  else
    ""

