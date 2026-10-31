import Def.Tactic.Attr.Basic'
import Initialize.Lean.Meta.Fun2Arrow
open Lean Lean.Meta


initialize registerBuiltinAttribute {
  name := `comm'
  descr := "Automatically generate the commutative version of an equality theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨parity, type, value⟩ ← Expr.comm' decl.type (.const declName (levelParams.map .param)) stx.getNum
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    println! s!"parity = {parity}"
    println! s!"moduleTokens = {moduleTokens}"
    let name := ((moduleTokens.comm parity).foldl Name.str default).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mp'
  descr := "Automatically generate the mp implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    Lean.logInfo s!"parity = {parity}"
    Lean.logInfo s!"and = {and}"
    let ⟨_, type, value⟩ ← Expr.mp' decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity (and := and)
    let moduleTokens := (← getEnv).moduleTokens
    let name :=
      if moduleTokens.contains "is" then
        (moduleTokens.mp.foldl Name.str default).lemmaName declName
      else
        match moduleTokens.replaceIffToken "Imp_" with
        | some tokens => (tokens.foldl Name.str default).lemmaName declName
        | none => (moduleTokens.mp.foldl Name.str default).lemmaName declName
    Lean.logInfo s!"name = {name}"
    Lean.logInfo s!"(← getEnv).moduleTokens = {(← getEnv).moduleTokens}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mpr'
  descr := "Automatically generate the mpr implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    let ⟨_, type, value⟩ ← Expr.mpr' decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity and
        let moduleTokens := (← getEnv).moduleTokens
    let name :=
      if moduleTokens.contains "is" then
        (moduleTokens.mpr.foldl Name.str default).lemmaName declName
      else
        match moduleTokens.replaceIffToken "Imp" with
        | some tokens => (tokens.foldl Name.str default).lemmaName declName
        | none => (moduleTokens.mpr.foldl Name.str default).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mp.comm'
  descr := "Automatically generate the commutative mp implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    let ⟨n, type, value⟩ ← Expr.mp' decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity (and := and)
    println! s!"n = {n}, 1 <<< n = {1 <<< n}"
    let ⟨parity, type, value⟩ ← Expr.comm' type value (1 <<< n)
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    let name := ((moduleTokens.mp.comm parity).foldl Name.str default).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mpr.comm'
  descr := "Automatically generate the commutative mpr implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    let ⟨n, type, value⟩ ← Expr.mpr' decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity and
    let ⟨parity, type, value⟩ ← Expr.comm' type value (1 <<< n)
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    let name := ((moduleTokens.mpr.comm parity).foldl Name.str default).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `comm.is'
  descr := "Automatically generate the commutative version of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams

    let proof : Lean.Expr := .const declName (levelParams.map .param)
    let ⟨n, type, value⟩ ← Expr.mpr' decl.type proof (and := true)
    let ⟨_, type, mpr⟩ := Expr.comm type value (1 <<< n)

    let ⟨n, type, value⟩ ← Expr.mp' decl.type proof (and := true)
    let ⟨_, type, mp⟩ := Expr.comm type value (1 <<< n)

    let ⟨parity, type, value⟩ ← Expr.comm.is' decl.type mp mpr stx.getNum
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    let name := List.comm.is moduleTokens parity
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := (name.foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `is.comm'
  descr := "Automatically generate the swapped commutative version of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams

    let proof : Lean.Expr := .const declName (levelParams.map .param)
    let ⟨n, type, value⟩ ← Expr.mpr' decl.type proof (and := true)
    let ⟨_, type, mpr⟩ := Expr.comm type value (1 <<< n)

    let ⟨n, type, value⟩ ← Expr.mp' decl.type proof (and := true)
    let ⟨_, type, mp⟩ := Expr.comm type value (1 <<< n)

    let ⟨parity, type, value⟩ ← Expr.is.comm' decl.type mp mpr stx.getNum
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    let name := List.is.comm moduleTokens parity
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := (name.foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mt'
  descr := "Automatically generate the contraposition (modus tollens) of an implication theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let constructor_order ← constructor_order declName
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    println! s!"parity = {parity}"
    let ⟨parity, type, value⟩ ← Expr.mt' decl.type (.const declName (levelParams.map .param)) parity
    let name := ((← getEnv).moduleTokens.mt constructor_order parity).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mp.mt'
  descr := "Automatically generate the mt version of the mp implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let constructor_order ← constructor_order declName
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    let ⟨_, type, value⟩ := Expr.mp decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity (and := and)
    let ⟨_, type, value⟩ ← Expr.mt' type value
    let moduleTokens := (← getEnv).moduleTokens.mp
    println! s!"moduleTokens.mp = {moduleTokens}"
    let name := (moduleTokens.mt constructor_order).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mpr.mt'
  descr := "Automatically generate the mt version of the mpr implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let constructor_order ← constructor_order declName
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let ⟨_, type, value⟩ ← Expr.mpr' decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity (stx.getIdent == `and)
    let ⟨_, type, value⟩ ← Expr.mt' type value
    let moduleTokens := (← getEnv).moduleTokens.mpr
    let name := (moduleTokens.mt constructor_order).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `is.mt'
  descr := "Automatically generate the mt version (both sides negated) of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ ← Expr.is.mt' decl.type (.const declName (levelParams.map .param))
    let name := (List.is.mt' (← getEnv).moduleTokens).foldl Name.str default |>.lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `left'
  descr := "Automatically generate the left introduction of a disjunction theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    println! s!"parity = {parity}"
    let ⟨parity, type, value⟩ ← Expr.disjunction' decl.type (.const declName (levelParams.map .param)) parity
    let name := ((← getEnv).moduleTokens.left).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `right'
  descr := "Automatically generate the right introduction of a disjunction theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    println! s!"parity = {parity}"
    let ⟨parity, type, value⟩ ← Expr.disjunction' decl.type (.const declName (levelParams.map .param)) parity false
    let name := ((← getEnv).moduleTokens.right).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mpr.left'
  descr := "Automatically generate the left introduction of a disjunction theorem from the mpr part of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    let ⟨_, type, value⟩ ← Expr.mpr' decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity and
    let moduleTokens := (← getEnv).moduleTokens.mpr
    println! s!"moduleTokens = {moduleTokens}"
    let ⟨parity, type, value⟩ ← Expr.disjunction' type value
    let name := moduleTokens.left.lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mpr.right'
  descr := "Automatically generate the right introduction of a disjunction theorem from the mpr part of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    let ⟨_, type, value⟩ ← Expr.mpr' decl.type (if parity > 0 then decl.proof else .const declName (levelParams.map .param)) parity and
    let moduleTokens := (← getEnv).moduleTokens.mpr
    println! s!"moduleTokens = {moduleTokens}"
    let ⟨parity, type, value⟩ ← Expr.disjunction' type value 0 false
    let name := moduleTokens.right.lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `fin'
  descr := "Automatically generate the theorem with .getElem substituted by .get"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ ← Expr.subst' decl.type (.const declName (levelParams.map .param)) Lean.Expr.getElem2get stx.getNum
    let name := (← getEnv).module.lemmaName declName
    let name := name.str "fin"
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `fin.comm'
  descr := "Automatically generate the comm theorem with .getElem substituted by .get"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ ← Expr.subst' decl.type (.const declName (levelParams.map .param)) Lean.Expr.getElem2get stx.getNum
    let ⟨parity, type, value⟩ ← Expr.comm' type value
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    println! s!"parity = {parity}"
    println! s!"moduleTokens = {moduleTokens}"
    let name := ((moduleTokens.comm parity).foldl Name.str default).lemmaName declName
    let name := name.str "fin"
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `fin.mp'
  descr := "Automatically generate the mp theorem with .getElem substituted by .get"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ ← Expr.subst' decl.type (.const declName (levelParams.map .param)) Lean.Expr.getElem2get stx.getNum
    let ⟨_, type, value⟩ ← Expr.mp' type value
    let name := ((← getEnv).moduleTokens.mp.foldl Name.str default).lemmaName declName
    let name := name.str "fin"
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `fin.mpr'
  descr := "Automatically generate the mpr theorem with .getElem substituted by .get"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ ← Expr.subst' decl.type (.const declName (levelParams.map .param)) Lean.Expr.getElem2get stx.getNum
    let ⟨_, type, value⟩ ← Expr.mpr' type value
    let name := ((← getEnv).moduleTokens.mpr.foldl Name.str default).lemmaName declName
    let name := name.str "fin"
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `val'
  descr := "Automatically generate the theorem with Fin type substituted by its val type"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ ← Expr.subst' decl.type (.const declName (levelParams.map .param)) Lean.Expr.fin2val stx.getNum
    let name := (← getEnv).module.lemmaName declName
    let name := name.str "val"
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `cast'
  descr := "Automatically generate the cast equality from an as / ≃ theorem (testing)."
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let comm := stx.getIdent != `false
    let parity := stx.getNum
    let ⟨parity, type, value⟩ ← Expr.cast' decl.type (.const declName (levelParams.map .param)) parity comm
    let name := (List.castPath (← getEnv).moduleTokens comm).foldl Name.str default |>.lemmaName declName
    println! s!"cast' name = {name}"
    println! s!"cast' type = {type}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `cast.comm'
  descr := "Automatically generate the commuted cast equality from an as / ≃ theorem (cast then comm, debug)."
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨_, castType, castValue⟩ ←
      Expr.cast' decl.type (.const declName (levelParams.map .param)) 0 true
    println! s!"cast.comm' after cast type = {castType}"
    let ⟨parity, type, value⟩ ← Expr.comm' castType castValue stx.getNum
    let ⟨_, parity⟩ ← parity.extractParity
    let name :=
      ((List.castPath (← getEnv).moduleTokens true |>.comm parity).foldl Name.str default).lemmaName
        declName
    println! s!"cast.comm' name = {name}"
    println! s!"cast.comm' type = {type}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `cast.fin'
  descr := "Automatically generate the cast equality from an as / ≃ theorem (testing)."
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let comm := stx.getIdent != `false
    let ⟨parity, type, value⟩ ← Expr.cast' decl.type (.const declName (levelParams.map .param)) stx.getNum comm
    let ⟨type, value⟩ ← Expr.subst' type value Lean.Expr.getElem2get stx.getNum
    let name := (List.castPath (← getEnv).moduleTokens comm).foldl Name.str default |>.lemmaName declName
    let name := name.str "fin"
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `debug
  descr := "debug"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    Lean.logInfo s!"decl.type = \n{decl.type.format}"
    Lean.logInfo s!"decl.proof = \n{decl.proof.format}"
}

initialize registerBuiltinAttribute {
  name := `subst'
  descr := "Automatically generate the theorem with OfNat literal substituted by a variable and Eq hypothesis (debug)."
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let lit := stx.getNum
    let ⟨type, value⟩ ← MetaM.run' <| Expr.substNat' decl.type (.const declName (levelParams.map .param)) lit
    let name := ((← getEnv).module.substModule lit).lemmaName declName
    println! s!"subst' name = {name}"
    println! s!"subst' type = {type.format}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[And.left']` — debug variant of the official `@[And.left]` attribute, kept in
`Basic'` for experimentation; it shares the same projection machinery
(`Expr.andProj` / `Name.andProjName`) defined in `Def.Tactic.Attr.Basic.Part2`.

`theorem Section.Type1.Type2.of.Givens (…): A ∧ B` generates
`theorem Section.Type1.of.Givens (…): A`, proved by `.1`.
When `Type1 = Type2` the generated name is `Section.Type1.of.Givens.fst`.
-/
initialize registerBuiltinAttribute {
  name := `And.left'
  descr := "Debug: extract the left conjunct of the conclusion (Type1.Type2.of.G → Type1.of.G, .fst when Type1 = Type2)"
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
`@[And.right']` — debug variant of the official `@[And.right]` attribute, kept in
`Basic'` for experimentation; it shares the same projection machinery
(`Expr.andProj` / `Name.andProjName`) defined in `Def.Tactic.Attr.Basic.Part2`.

`theorem Section.Type1.Type2.of.Givens (…): A ∧ B` generates
`theorem Section.Type2.of.Givens (…): B`, proved by `.2`.
When `Type1 = Type2` the generated name is `Section.Type2.of.Givens.snd`.
-/
initialize registerBuiltinAttribute {
  name := `And.right'
  descr := "Debug: extract the right conjunct of the conclusion (Type1.Type2.of.G → Type2.of.G, .snd when Type1 = Type2)"
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
`@[And.right.left']` — debug variant of `@[And.right.left]`.
-/
initialize registerBuiltinAttribute {
  name := `And.right.left'
  descr := "Debug: extract And.right then And.left (Type1.Type2.Type3.of.G → Type2.of.G)"
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
`@[And.right.right']` — debug variant of `@[And.right.right]`.
-/
initialize registerBuiltinAttribute {
  name := `And.right.right'
  descr := "Debug: extract And.right then And.right (Type1.Type2.Type3.of.G → Type3.of.G)"
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
`@[mp.left']` — debug mirror of the production `@[mp.left]`. Identical body
shape but uses `Expr.mp'` (which logs intermediate steps) and re-uses the
production name helper `Name.mpProjName` from `Def.Tactic.Attr.Basic.Part2`.
-/
initialize registerBuiltinAttribute {
  name := `mp.left'
  descr := "Debug mirror of @[mp.left]; uses Expr.mp' with logging"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    Lean.logInfo s!"[mp.left'] declName = {declName}, parity = {parity}, and = {and}"
    let ⟨_, mpType, mpValue⟩ ←
      Expr.mp' decl.type
        (if parity > 0 then decl.proof
         else .const declName (levelParams.map .param))
        parity (and := and)
    Lean.logInfo s!"[mp.left'] mpType = {mpType}"
    let (type, value) := Expr.andProj mpType mpValue true
    Lean.logInfo s!"[mp.left'] final type = {type}"
    let name := Name.mpProjName (← getEnv).moduleTokens declName true
    Lean.logInfo s!"[mp.left'] name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[mp.right']` — debug mirror of the production `@[mp.right]`. Identical body
shape but uses `Expr.mp'` (which logs intermediate steps) and re-uses the
production name helper `Name.mpProjName` from `Def.Tactic.Attr.Basic.Part2`.
-/
initialize registerBuiltinAttribute {
  name := `mp.right'
  descr := "Debug mirror of @[mp.right]; uses Expr.mp' with logging"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    Lean.logInfo s!"[mp.right'] declName = {declName}, parity = {parity}, and = {and}"
    let ⟨_, mpType, mpValue⟩ ←
      Expr.mp' decl.type
        (if parity > 0 then decl.proof
         else .const declName (levelParams.map .param))
        parity (and := and)
    Lean.logInfo s!"[mp.right'] mpType = {mpType}"
    let (type, value) := Expr.andProj mpType mpValue false
    Lean.logInfo s!"[mp.right'] final type = {type}"
    let name := Name.mpProjName (← getEnv).moduleTokens declName false
    Lean.logInfo s!"[mp.right'] name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `Fun'
  descr := "Automatically generate the theorem with Fun/⇀ binders as bare arrows and GetElem as application (debug Fun')."
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ := Expr.substFun decl.type (.const declName (levelParams.map .param)) stx.getNum
    let name := ((← getEnv).module.lemmaName declName).str "fun"
    println! s!"Fun' name = {name}"
    println! s!"Fun' type = {type}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}
