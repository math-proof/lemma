import Def.Tactic.Attr.Basic.Part2
open Lean
open Lean.Meta


/--
Registers a custom attribute `@[path]` that, when applied to a theorem or definition,
exports a private lemma under a public name derived from the source file path
and the original declaration name.

- The new name is constructed by:
  1. Removing the main module name from the path.
  2. Appending a lowercased suffix of the original declaration name.
  3. Omitting the suffix if it is `main`.

This is useful for automatically generating namespaced lemmas from file structure,
helpful in large-scale automated lemma generation systems.

Example:
If `MyLib.Group.Basic` contains `def Main`, the resulting name will be `Group.Basic`.
If it contains `def LeftId`, the resulting name will be `Group.Basic.leftid`.

Usage:
```lean
@[path]
lemma MyLemma : ...
```
-/
initialize registerBuiltinAttribute {
  name := `path
  descr := "An attribute that exports a private lemma under a file-path-based public name"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    addDecl <| .defnDecl {
      name := (← getEnv).module.lemmaName declName
      levelParams := levelParams
      type := decl.type
      value := .const declName (levelParams.map .param)
      hints := .abbrev
      safety := .safe
    }
}

/--
`@[comm]` (abbreviated from `law of commutativity` : 交换律) attribute automatically generates the symmetric version of a theorem if it proves an equality.

Usage:
```lean
@[comm]
theorem Section.LHS.eq.RHS {c : γ} (a : α) (b : β) : lhs a b = rhs a b := by proof
-- Generates:
theorem Section.RHS.eq.LHS {c : γ} (a : α) (b : β) : rhs a b = lhs a b := (Section.LHS.eq.RHS a b).symm

@[comm 6]
theorem Section.LHS.eq.RHS.of.Eq.Eq.Eq (h₀ : α = α') (h₁ : β = β') (h₂ : γ = γ'): lhs h₀ h₁ h₂ = rhs h₀ h₁ h₂ := by proof
-- 6 is decomposed as binary digits : 110 => [0, 1, 1], where each bit represents whether the corresponding default binder is commutated or not.
Generates:
theorem Section.RHS.eq.LHS.of.Eq.Eq.Eq (h₀ : α' = α) (h₁ : β' = β) (h₂ : γ = γ'): lhs h₀.symm h₁.symm h₂ = rhs h₀.symm h₁.symm h₂ := (Section.LHS.eq.RHS.of.Eq.Eq.Eq h₀.symm h₁.symm h₂).symm
```
-/
initialize registerBuiltinAttribute {
  name := `comm
  descr := "Automatically generate the commutative version of an equality theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨parity, type, value⟩ := Expr.comm decl.type (.const declName (levelParams.map .param)) stx.getNum
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    addAndCompile <| .thmDecl {
      name := ((moduleTokens.comm parity).foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[mp]` (abbreviated from `modus ponens`) attribute automatically generates the mp implication of a equivalence theorem.
Usage:
```lean
@[mp]
theorem Section.LHS.is.RHS {c : γ} (a : α) (b : β) : lhs a b ↔ rhs a b := ⟨proof.mp, proof.mpr⟩
-- Generates:
theorem Section.RHS.of.LHS {c : γ} {a : α} {b : β} (h : lhs a b): rhs a b := (Section.LHS.eq.RHS a b).mp h

@[mp 4]
theorem Section.LHS.is.RHS [Class_0 α] [Class_1 α] [Class_2 α] {c : γ} (a : α) (b : β) : lhs a b ↔ rhs a b := by proof
-- 4 is decomposed as binary digits : 100 => [0, 0, 1], where each bit represents whether the corresponding instImplicit binder is filtered.
Generates:
theorem Section.RHS.of.LHS [Class_0 α] [Class_1 α] {c : γ} {a : α} {b : β} (h : lhs a b): rhs a b := proof.mp h
```
notice that the default dependent arguments (a : α) (b : β) are made implicit {a : α} {b : β}
-/
initialize registerBuiltinAttribute {
  name := `mp
  descr := "Automatically generate the mp implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let ⟨_, type, value⟩ := Expr.mp decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity (and := stx.getIdent == `and)
    let moduleTokens := (← getEnv).moduleTokens
    let name :=
      if moduleTokens.contains "is" then
        (moduleTokens.mp.foldl Name.str default).lemmaName declName
      else
        match moduleTokens.replaceIffToken "Imp_" with
        | some tokens => (tokens.foldl Name.str default).lemmaName declName
        | none => (moduleTokens.mp.foldl Name.str default).lemmaName declName
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[mpr]` (abbreviated from `modus ponens reverse`) attribute automatically generates the mpr implication of a equivalence theorem.
Usage:
```lean
@[mpr]
theorem Section.LHS.is.RHS {c : γ} (a : α) (b : β) : lhs a b ↔ rhs a b := by proof
-- Generates:
theorem Section.LHS.of.RHS {c : γ} {a : α} {b : β} (h : rhs a b) : lhs a b := (Section.LHS.eq.RHS a b).mpr h
```
-/
initialize registerBuiltinAttribute {
  name := `mpr
  descr := "Automatically generate the mpr implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let ⟨_, type, value⟩ := Expr.mpr decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity (stx.getIdent == `and)
    let moduleTokens := (← getEnv).moduleTokens
    let name :=
      if moduleTokens.contains "is" then
        (moduleTokens.mpr.foldl Name.str default).lemmaName declName
      else
        match moduleTokens.replaceIffToken "Imp" with
        | some tokens => (tokens.foldl Name.str default).lemmaName declName
        | none => (moduleTokens.mpr.foldl Name.str default).lemmaName declName
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[mp.comm]` attribute automatically generates the commutative mp implication of a equivalence theorem.
Usage:
```lean
@[mp.comm]
theorem Section.LHS.is.RHS {c : γ} (a : α) (b : β) : lhs a b ↔ a = b := by proof
-- Generates:
theorem Section.RHS'.of.LHS {c : γ} {a : α} {b : β} (h : lhs a b) : b = a := (Section.LHS.eq.RHS a b).mp.symm
```
-/
initialize registerBuiltinAttribute {
  name := `mp.comm
  descr := "Automatically generate the commutative mp implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let ⟨n, type, value⟩ := Expr.mp decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity (and := stx.getIdent == `and)
    -- 2ⁿ, where n is the number of default binders
    let ⟨parity, type, value⟩ := Expr.comm type value (1 <<< n)
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    addAndCompile <| .thmDecl {
      name := ((moduleTokens.mp.comm parity).foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[mpr.comm]` attribute automatically generates the commutative mpr implication of a equivalence theorem.
Usage:
```lean
@[mpr.comm]
theorem Section.LHS.is.RHS {c : γ} (a : α) (b : β) : a = b ↔ rhs a b := by proof
-- Generates:
theorem Section.LHS'.of.RHS {c : γ} {a : α} {b : β} (h : rhs a b) : b = a := (Section.LHS.eq.RHS a b).mpr.symm
```
-/
initialize registerBuiltinAttribute {
  name := `mpr.comm
  descr := "Automatically generate the commutative mpr implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let ⟨n, type, value⟩ := Expr.mpr decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity (stx.getIdent == `and)
    let ⟨parity, type, value⟩ := Expr.comm type value (1 <<< n)
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    addAndCompile <| .thmDecl {
      name := ((moduleTokens.mpr.comm parity).foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[comm.is]` attribute automatically generates the commutative version of an equivalence (Iff) theorem.
Usage:
```lean
@[mpr]
theorem Section.LHS.is.RHS (a : α) (b : β) : a ≃ b ↔ a' = b' := by proof
-- Generates:
theorem Section.LHS'.is.RHS' {a : α} {b : β} : b ≃ a ↔ b' = a' := ⟨mr.comm, mpr.comm⟩
```
-/
initialize registerBuiltinAttribute {
  name := `comm.is
  descr := "Automatically generate the commutative version of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams

    let proof := .const declName (levelParams.map .param)
    let ⟨n, type, value⟩ := Expr.mpr decl.type proof (and := true)
    let ⟨_, type, mpr⟩ := Expr.comm type value (1 <<< n)

    let ⟨n, type, value⟩ := Expr.mp decl.type proof (and := true)
    let ⟨_, type, mp⟩ := Expr.comm type value (1 <<< n)

    let ⟨parity, type, value⟩ := Expr.comm.is decl.type mp mpr stx.getNum
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    addAndCompile <| .thmDecl {
      name := ((List.comm.is moduleTokens parity).foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[is.comm]` attribute automatically generates the swapped commutative version of an equivalence (Iff) theorem.
Usage:
```lean
@[mpr]
theorem Section.LHS.is.RHS (a : α) (b : β) : a ≃ b ↔ a' = b' := by proof
-- Generates:
theorem Section.RHS'.is.LHS' {a : α} {b : β} : b' = a' ↔ b ≃ a := ⟨mpr.comm, mp.comm⟩
```
-/
initialize registerBuiltinAttribute {
  name := `is.comm
  descr := "Automatically generate the swapped commutative version of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams

    let proof := .const declName (levelParams.map .param)
    let ⟨n, type, value⟩ := Expr.mpr decl.type proof (and := true)
    let ⟨_, type, mpr⟩ := Expr.comm type value (1 <<< n)

    let ⟨n, type, value⟩ := Expr.mp decl.type proof (and := true)
    let ⟨_, type, mp⟩ := Expr.comm type value (1 <<< n)

    let ⟨parity, type, value⟩ := Expr.is.comm decl.type mp mpr stx.getNum
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    addAndCompile <| .thmDecl {
      name := ((List.is.comm moduleTokens parity).foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[mt]` (abbreviated from `modus tollens`) attribute automatically generates the mt version of an implication theorem.
Usage:
```lean
@[mt]
theorem Section.LHS.of.RHS {a : α} {b : β} (h : lhs a b) : rhs a b := proof
-- Generates:
theorem Section.NotRHS.of.NotLHS {a : α} {b : β} (h : ¬rhs a b): ¬lhs a b := mt Section.LHS.of.RHS h
```
-/
initialize registerBuiltinAttribute {
  name := `mt
  descr := "Automatically generate the contraposition (modus tollens) of an implication theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let constructor_order ← constructor_order declName
    let levelParams := decl.levelParams
    let ⟨index, type, value⟩ := Expr.mt decl.type (.const declName (levelParams.map .param)) stx.getNum
    addAndCompile <| .thmDecl {
      name := ((← getEnv).moduleTokens.mt constructor_order index).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[mp.mt]` attribute automatically generates the mt version of an mp implication from an equivalence theorem.
Usage:
```lean
@[mp.mt]
theorem Section.LHS.is.RHS {a : α} {b : β} : lhs a b ↔ rhs a b := proof
-- Generates:
theorem Section.NotLHS.of.NotRHS {a : α} {b : β} (h : ¬rhs a b): ¬lhs a b := mt Section.LHS.is.RHS.mp h
```
-/
initialize registerBuiltinAttribute {
  name := `mp.mt
  descr := "Automatically generate the mt version of the mp implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let constructor_order ← constructor_order declName
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let ⟨_, type, value⟩ := Expr.mp decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity (and := stx.getIdent == `and)
    let ⟨_, type, value⟩ := Expr.mt type value
    let moduleTokens := (← getEnv).moduleTokens.mp
    addAndCompile <| .thmDecl {
      name := (moduleTokens.mt constructor_order).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[mpr.mt]` attribute automatically generates the mt version of an mp implication from an equivalence theorem.
Usage:
```lean
@[mpr.mt]
theorem Section.LHS.is.RHS {a : α} {b : β} : lhs a b ↔ rhs a b := proof
-- Generates:
theorem Section.NotRHS.of.NotLHS {a : α} {b : β} (h : ¬lhs a b): ¬rhs a b := mt Section.LHS.is.RHS.mpr h
```
-/
initialize registerBuiltinAttribute {
  name := `mpr.mt
  descr := "Automatically generate the mt version of the mpr implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let constructor_order ← constructor_order declName
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let ⟨_, type, value⟩ := Expr.mpr decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity (stx.getIdent == `and)
    let ⟨_, type, value⟩ := Expr.mt type value
    let moduleTokens := (← getEnv).moduleTokens.mpr
    addAndCompile <| .thmDecl {
      name := (moduleTokens.mt constructor_order).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[is.mt]` attribute automatically generates the mt version (both sides negated) of an equivalence theorem.
Usage:
```lean
@[is.mt]
theorem Section.LHS.is.RHS {a : α} {b : β} : lhs a b ↔ rhs a b := proof
-- Generates:
theorem Section.NotLHS.is.NotRHS {a : α} {b : β} : ¬lhs a b ↔ ¬rhs a b := (Section.LHS.is.RHS a b).not
```
-/
initialize registerBuiltinAttribute {
  name := `is.mt
  descr := "Automatically generate the mt version (both sides negated) of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ := Expr.is.mt decl.type (.const declName (levelParams.map .param))
    addAndCompile <| .thmDecl {
      name := (List.is.mt (← getEnv).moduleTokens).foldl Name.str default |>.lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `Or.inl
  descr := "Automatically generate the left introduction of a disjunction theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let ⟨parity, type, value⟩ := Expr.disjunction decl.type (.const declName (levelParams.map .param)) parity
    addAndCompile <| .thmDecl {
      name := ((← getEnv).moduleTokens.left).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `Or.inr
  descr := "Automatically generate the right introduction of a disjunction theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let ⟨parity, type, value⟩ := Expr.disjunction decl.type (.const declName (levelParams.map .param)) parity false
    addAndCompile <| .thmDecl {
      name := ((← getEnv).moduleTokens.right).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[And.left]` extracts the left conjunct of a theorem's conjunctive conclusion.

`theorem Section.Type1.Type2.of.Givens (…): A ∧ B` generates
`theorem Section.Type1.of.Givens (…): A`, proved by `.1`.
When `Type1 = Type2` the generated name is `Section.Type1.of.Givens.fst`.

For a triple `Type1.Type2.Type3.of.Givens` (`A ∧ B ∧ C`), generates
`Section.Type1.of.Givens`; when `Type1 = Type2` the name is
`Section.Type1.of.Givens.fst`.
-/
initialize registerBuiltinAttribute {
  name := `And.left
  descr := "Extract the left conjunct (Type1.Type2.of.G → Type1.of.G; triple → Type1.of.G.fst when Type1 = Type2)"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let (type, value) :=
      Expr.andProj decl.type (.const declName (decl.levelParams.map .param)) true
    addAndCompile <| .thmDecl {
      name := Name.andProjName (← getEnv).moduleTokens declName true
      levelParams := decl.levelParams
      type := type
      value := value
    }
}

/--
`@[And.right]` extracts the right conjunct of a theorem's conjunctive conclusion.

`theorem Section.Type1.Type2.of.Givens (…): A ∧ B` generates
`theorem Section.Type2.of.Givens (…): B`, proved by `.2`.
When `Type1 = Type2` the generated name is `Section.Type2.of.Givens.snd`.
-/
initialize registerBuiltinAttribute {
  name := `And.right
  descr := "Extract the right conjunct of the conclusion (Type1.Type2.of.G → Type2.of.G, .snd when Type1 = Type2)"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let (type, value) :=
      Expr.andProj decl.type (.const declName (decl.levelParams.map .param)) false
    addAndCompile <| .thmDecl {
      name := Name.andProjName (← getEnv).moduleTokens declName false
      levelParams := decl.levelParams
      type := type
      value := value
    }
}

/--
`@[And.right.left]` extracts the left of the right conjunct of a right-associative
triple conclusion (`A ∧ B ∧ C = A ∧ (B ∧ C)` → `B`).

`theorem Section.Type1.Type2.Type3.of.Givens (…): A ∧ B ∧ C` generates
`theorem Section.Type2.of.Givens (…): B`, proved by `.2.1`.
When `Type2 = Type3` the generated name is `Section.Type2.of.Givens.snd.fst`.
-/
initialize registerBuiltinAttribute {
  name := `And.right.left
  descr := "Extract And.right then And.left (Type1.Type2.Type3.of.G → Type2.of.G, .snd.fst when Type2 = Type3)"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let value0 := .const declName (decl.levelParams.map .param)
    let (type1, value1) := Expr.andProj decl.type value0 false
    let (type, value) := Expr.andProj type1 value1 true
    addAndCompile <| .thmDecl {
      name := Name.andRightProjName (← getEnv).moduleTokens declName true
      levelParams := decl.levelParams
      type := type
      value := value
    }
}

/--
`@[And.right.right]` extracts the right of the right conjunct of a right-associative
triple conclusion (`A ∧ B ∧ C = A ∧ (B ∧ C)` → `C`).

`theorem Section.Type1.Type2.Type3.of.Givens (…): A ∧ B ∧ C` generates
`theorem Section.Type3.of.Givens (…): C`, proved by `.2.2`.
When `Type2 = Type3` the generated name is `Section.Type3.of.Givens.snd.snd`.
-/
initialize registerBuiltinAttribute {
  name := `And.right.right
  descr := "Extract And.right then And.right (Type1.Type2.Type3.of.G → Type3.of.G, .snd.snd when Type2 = Type3)"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let value0 := .const declName (decl.levelParams.map .param)
    let (type1, value1) := Expr.andProj decl.type value0 false
    let (type, value) := Expr.andProj type1 value1 false
    addAndCompile <| .thmDecl {
      name := Name.andRightProjName (← getEnv).moduleTokens declName false
      levelParams := decl.levelParams
      type := type
      value := value
    }
}

/--
`@[mp.left]` applies `@[mp]` to an equivalence and then projects the LEFT
conjunct of the resulting `∧`-conclusion.

For `theorem Section.Type1.is.Type2.Type3 (…): A ↔ (B ∧ C)` generates
`theorem Section.Type2.of.Type1 (…): A → B`, proved by `.mp.left`.
When `Type2 = Type3` the generated name carries a `.fst` suffix.
-/
initialize registerBuiltinAttribute {
  name := `mp.left
  descr := "Apply mp to an equivalence, then project the LEFT conjunct (Int.LtAbs.is.LtNeg.Lt → Int.LtNeg.of.LtAbs)"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    -- Step 1: mp (P ↔ Q  →  P → Q)
    let ⟨_, mpType, mpValue⟩ :=
      Expr.mp decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param))
        parity (and := stx.getIdent == `and)
    -- Step 2: And.left on the result (P → B ∧ C  →  P → B)
    let (type, value) := Expr.andProj mpType mpValue true
    addAndCompile <| .thmDecl {
      name := Name.mpProjName (← getEnv).moduleTokens declName true
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[mp.right]` applies `@[mp]` to an equivalence and then projects the RIGHT
conjunct of the resulting `∧`-conclusion.

For `theorem Section.Type1.is.Type2.Type3 (…): A ↔ (B ∧ C)` generates
`theorem Section.Type3.of.Type1 (…): A → C`, proved by `.mp.right`.
When `Type2 = Type3` the generated name carries a `.snd` suffix.
-/
initialize registerBuiltinAttribute {
  name := `mp.right
  descr := "Apply mp to an equivalence, then project the RIGHT conjunct (Int.LtAbs.is.LtNeg.Lt → Int.Lt.of.LtAbs)"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let ⟨_, mpType, mpValue⟩ :=
      Expr.mp decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param))
        parity (and := stx.getIdent == `and)
    let (type, value) := Expr.andProj mpType mpValue false
    addAndCompile <| .thmDecl {
      name := Name.mpProjName (← getEnv).moduleTokens declName false
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mpr.left
  descr := "Automatically generate the left introduction of a disjunction theorem from the mpr part of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    let ⟨_, type, value⟩ := Expr.mpr decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity and
    let moduleTokens := (← getEnv).moduleTokens.mpr
    let ⟨parity, type, value⟩ := Expr.disjunction type value
    let name := moduleTokens.left.lemmaName declName
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mpr.right
  descr := "Automatically generate the right introduction of a disjunction theorem from the mpr part of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    let ⟨_, type, value⟩ := Expr.mpr decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity and
    let moduleTokens := (← getEnv).moduleTokens.mpr
    let ⟨parity, type, value⟩ := Expr.disjunction type value 0 false
    let name := moduleTokens.right.lemmaName declName
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[fin]` attribute automatically generates the fin version of a theorem

Usage:
```lean
@[fin 1]
theorem Section.UFnGet {s : List α} {b : List α} {i j : ℕ} (h : f s[j] = g b[i]) : f s[i] = g b[j] := by proof
-- Generates:
theorem Section.UFnGet.fin {s : List α} {b : List α} {i j : ℕ} (h : f (s.get ⟨j, by grind⟩) = g (b.get ⟨i, by grind⟩)) : f (s.get ⟨i, by grind⟩) = g (b.get ⟨j, by grind⟩) := by sorry
```
-/
initialize registerBuiltinAttribute {
  name := `fin
  descr := "Automatically generate the theorem with .getElem substituted by .get"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ := Expr.subst decl.type (.const declName (levelParams.map .param)) Expr.getElem2get stx.getNum
    addAndCompile <| .thmDecl {
      name := ((← getEnv).module.lemmaName declName).str "fin"
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `fin.comm
  descr := "Automatically generate the comm theorem with .getElem substituted by .get"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ := Expr.subst decl.type (.const declName (levelParams.map .param)) Expr.getElem2get stx.getNum
    let ⟨parity, type, value⟩ := Expr.comm type value
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    addAndCompile <| .thmDecl {
      name := (((moduleTokens.comm parity).foldl Name.str default).lemmaName declName).str "fin"
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `fin.mp
  descr := "Automatically generate the mp theorem with .getElem substituted by .get"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ := Expr.subst decl.type (.const declName (levelParams.map .param)) Expr.getElem2get stx.getNum
    let ⟨_, type, value⟩ := Expr.mp type value
    addAndCompile <| .thmDecl {
      name := (((← getEnv).moduleTokens.mp.foldl Name.str default).lemmaName declName).str "fin"
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `fin.mpr
  descr := "Automatically generate the mpr theorem with .getElem substituted by .get"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ := Expr.subst decl.type (.const declName (levelParams.map .param)) Expr.getElem2get stx.getNum
    let ⟨_, type, value⟩ := Expr.mpr type value
    addAndCompile <| .thmDecl {
      name := (((← getEnv).moduleTokens.mpr.foldl Name.str default).lemmaName declName).str "fin"
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[val]` attribute automatically generates the val version of a theorem

Usage:
```lean
@[val]
theorem Section.UFnGet {a : List.Vector α n} (b : List.Vector α n) (i j : Fin n) : f a[i] = g b[j] := by proof
-- Generates:
theorem Section.UFnGet.val {a : List.Vector α n} (b : List.Vector α n) (i j : Fin n) : f a[i.val] = g b[j.val] := by proof
```
-/
initialize registerBuiltinAttribute {
  name := `val
  descr := "Automatically generate the theorem with Fin type substituted by its val type"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ := Expr.subst decl.type (.const declName (levelParams.map .param)) Expr.fin2val stx.getNum
    addAndCompile <| .thmDecl {
      name := ((← getEnv).module.lemmaName declName).str "val"
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[subst]` automatically generates a theorem that replaces an `OfNat` literal by a variable.

Usage:
```lean
@[subst 1]
theorem Nat.EqMul_1 [MulOneClass M] (a : M) : a * 1 = a := mul_one a
-- Generates `Nat.EqMul_1.of.Eq_1`:
--   ∀ {M} {n : M} [MulOneClass M] (h : n = 1) (a : M), a * n = a
-- `n` and `h` are inserted before the first `()` given binder (default `BinderInfo`), or at index 0.
```
-/
initialize registerBuiltinAttribute {
  name := `subst
  descr := "Automatically generate the theorem with an OfNat literal substituted by a variable and an Eq hypothesis"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let lit := stx.getNum
    let ⟨type, value⟩ ← MetaM.run' <| Expr.substNat decl.type (.const declName (levelParams.map .param)) lit
    let name := ((← getEnv).module.substModule lit).lemmaName declName
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[cast]` automatically generates the cast equality from an `as` / `≃` theorem.
Usage:
```lean
@[cast]
theorem Section.as.UFn_0 (u : Fin 1 → List.Vector α n) : lhs ≃ rhs := by proof
-- Generates `Section.eq.Cast_UFn_0` with proof `Bool.Eq_Cast.of.SEq (Section.as.UFn_0 …)`.
```
-/
initialize registerBuiltinAttribute {
  name := `cast
  descr := "Automatically generate the cast equality from an as / ≃ theorem."
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let comm := stx.getIdent != `false
    let parity := stx.getNum
    let ⟨parity, type, value⟩ := Expr.cast decl.type (.const declName (levelParams.map .param)) parity comm
    let name := (List.castPath (← getEnv).moduleTokens comm).foldl Name.str default |>.lemmaName declName
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[cast.comm]` generates the commuted cast equality from an `as` / `≃` theorem.

It applies `@[cast]` then `@[comm]`:
`LHS.as.RHS` → `LHS.eq.Cast_RHS` → `Cast_RHS.eq.LHS`

Usage:
```lean
@[cast.comm]
theorem Section.LHS.as.RHS ... : lhs ≃ rhs := by proof
-- Generates `Section.Cast_RHS.eq.LHS` : Cast_RHS = LHS
```
-/
initialize registerBuiltinAttribute {
  name := `cast.comm
  descr := "Automatically generate the commuted cast equality from an as / ≃ theorem (cast then comm)."
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨_, castType, castValue⟩ :=
      Expr.cast decl.type (.const declName (levelParams.map .param)) 0 true
    let ⟨parity, type, value⟩ := Expr.comm castType castValue stx.getNum
    let ⟨_, parity⟩ ← parity.extractParity
    let name :=
      ((List.castPath (← getEnv).moduleTokens true |>.comm parity).foldl Name.str default).lemmaName
        declName
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `cast.fin
  descr := "Automatically generate the cast.fin equality from an as / ≃ theorem."
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let comm := stx.getIdent != `false
    let ⟨parity, type, value⟩ := Expr.cast decl.type (.const declName (levelParams.map .param)) stx.getNum comm
    let ⟨type, value⟩ := Expr.subst type value Lean.Expr.getElem2get stx.getNum
    let name := (List.castPath (← getEnv).moduleTokens comm).foldl Name.str default |>.lemmaName declName
    let name := name.str "fin"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}
