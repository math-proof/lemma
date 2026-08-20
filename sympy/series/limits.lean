import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
open Lean
open scoped Topology

/-- `x → ∞` — x is infinite. -/
syntax (name := tendsToInf) term:26 " → " "∞" : term
macro_rules (kind := tendsToInf)
  | `($x → ∞) => `(ArchimedeanClass.mk $x < 0)

/-- `x → 0` — x is infinitesimal. -/
syntax (name := tendsToZero) term:26 " → " num : term
macro_rules (kind := tendsToZero)
  | `($x → 0) => `(0 < ArchimedeanClass.mk $x)

private partial def isZeroSyntax? : Syntax → Bool
  | `(0) => true
  | `(OfNat.ofNat $_ 0 $_) => true
  | stx =>
    match stx with
    | .atom _ val => val == "0"
    | _ => false

private partial def archimedeanMkArg? : Syntax → Option Syntax
  | `(ArchimedeanClass.mk $x) => some x
  | `(@ArchimedeanClass.mk $_ $x) => some x
  | stx =>
    match stx with
    | .node _ `ArchimedeanClass.mk args =>
      if 0 < args.size then some args[args.size - 1]! else none
    | _ => none

@[app_unexpander LT.lt]
def tendsToLt.unexpand : PrettyPrinter.Unexpander
  | `($_ $a $b) =>
    if let some x := archimedeanMkArg? a then
      if isZeroSyntax? b then
        let x : TSyntax `term := ⟨x⟩
        `(($x → ∞))
      else
        throw ()
    else if isZeroSyntax? a then
      match archimedeanMkArg? b with
      | some x =>
        let x : TSyntax `term := ⟨x⟩
        `(($x → 0))
      | none => throw ()
    else
      throw ()
  | _ =>
    throw ()

/-- `x → +∞` — x is positive infinite. -/
syntax (name := tendsToPosInf) term:26 " → " "+" "∞" : term
macro_rules (kind := tendsToPosInf)
  | `($x → +∞) => `(0 < $x ∧ ArchimedeanClass.mk $x < 0)

/-- `x → -∞` — x is negative infinite. -/
syntax (name := tendsToNegInf) term:26 " → " "-" "∞" : term
macro_rules (kind := tendsToNegInf)
  | `($x → -∞) => `($x < 0 ∧ ArchimedeanClass.mk $x < 0)

/-- `x → 0⁺` — x is a positive infinitesimal (`0⁺`). -/
syntax (name := tendsToZeroPos) term:26 " → " num "⁺" : term
macro_rules (kind := tendsToZeroPos)
  | `($x → 0⁺) => `(0 < $x ∧ 0 < ArchimedeanClass.mk $x)

/-- `x → 0⁻` — x is a negative infinitesimal (`0⁻`). -/
syntax (name := tendsToZeroNeg) term:26 " → " num "⁻" : term
macro_rules (kind := tendsToZeroNeg)
  | `($x → 0⁻) => `($x < 0 ∧ 0 < ArchimedeanClass.mk $x)

private partial def unparenTerm? : Syntax → Syntax
  | `(term| ($t)) => t
  | stx => stx

private partial def asTendsToZero? : Syntax → Option Syntax
  | `($x → 0) => some x
  | stx =>
    match unparenTerm? stx with
    | `($x → 0) => some x
    | _ => none

private partial def asTendsToInf? : Syntax → Option Syntax
  | `($x → ∞) => some x
  | stx =>
    match unparenTerm? stx with
    | `($x → ∞) => some x
    | _ => none

@[app_unexpander And]
def tendsToPosNeg.unexpand : PrettyPrinter.Unexpander
  | `($_ $a $b) =>
    match a with
    | `(0 < $x) =>
      match asTendsToInf? b with
      | some y =>
        if x == y then
          let y : TSyntax `term := ⟨y⟩
          `($y → +∞)
        else
          throw ()
      | none =>
        match asTendsToZero? b with
        | some y =>
          if x == y then
            let y : TSyntax `term := ⟨y⟩
            `($y → 0⁺)
          else
            throw ()
        | none => throw ()
    | `($x < $zero) =>
      match zero with
      | `(0) =>
        match asTendsToInf? b with
        | some y =>
          if x == y then
            let y : TSyntax `term := ⟨y⟩
            `($y → -∞)
          else
            throw ()
        | none =>
          match asTendsToZero? b with
          | some y =>
            if x == y then
              let y : TSyntax `term := ⟨y⟩
              `($y → 0⁻)
            else
              throw ()
          | none => throw ()
      | _ =>
        throw ()
    | _ =>
      throw ()
  | _ =>
    throw ()

/-- `lim [n → ∞] e` — limit of `e` as `n` tends to `+∞` (`atTop`).
The type of `n` is inferred, or written `lim [(n : α) → ∞] e`.
Expands to `Filter.limUnder Filter.atTop fun n => e`. -/
macro:max (priority := 1003) "lim " "[" n:binderIdent " → " "∞" "] " e:term:67 : term =>
  match n with
  | `(binderIdent| _) => `(Filter.limUnder Filter.atTop fun _ => $e)
  | `(binderIdent| $n:ident) => `(Filter.limUnder Filter.atTop fun $n => $e)
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 1003) "lim " "[" "(" n:ident " : " ty:term ")" " → " "∞" "] " e:term:67 : term =>
  `(Filter.limUnder Filter.atTop fun $n : $ty => $e)

/-- `lim [n → -∞] e` — limit of `e` as `n` tends to `-∞` (`atBot`).
The type of `n` is inferred, or written `lim [(n : α) → -∞] e`.
Expands to `Filter.limUnder Filter.atBot fun n => e`. -/
macro:max (priority := 1003) "lim " "[" n:binderIdent " → " "-" "∞" "] " e:term:67 : term =>
  match n with
  | `(binderIdent| _) => `(Filter.limUnder Filter.atBot fun _ => $e)
  | `(binderIdent| $n:ident) => `(Filter.limUnder Filter.atBot fun $n => $e)
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 1003) "lim " "[" "(" n:ident " : " ty:term ")" " → " "-" "∞" "] " e:term:67 : term =>
  `(Filter.limUnder Filter.atBot fun $n : $ty => $e)

/-- `lim [x → 0] e` — two-sided limit as `x` tends to `0` (`𝓝[≠] 0`).
The type of `x` is inferred, or written `lim [(x : α) → 0] e`. -/
macro:max (priority := 1003) "lim " "[" n:binderIdent " → " z:num "] " e:term:67 : term =>
  match z with
  | `(num| 0) =>
    match n with
    | `(binderIdent| _) => `(Filter.limUnder (nhdsWithin 0 {0}ᶜ) fun _ => $e)
    | `(binderIdent| $n:ident) => `(Filter.limUnder (nhdsWithin 0 {0}ᶜ) fun $n => $e)
    | _ => Lean.Macro.throwUnsupported
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 1003) "lim " "[" "(" n:ident " : " ty:term ")" " → " z:num "] " e:term:67 : term =>
  match z with
  | `(num| 0) => `(Filter.limUnder (nhdsWithin (0 : $ty) {(0 : $ty)}ᶜ) fun $n : $ty => $e)
  | _ => Lean.Macro.throwUnsupported

/-- `lim [x → 0⁺] e` — right-hand limit as `x` tends to `0` (`𝓝[>] 0`).
The type of `x` is inferred, or written `lim [(x : α) → 0⁺] e`. -/
macro:max (priority := 1003) "lim " "[" n:binderIdent " → " z:num "⁺" "] " e:term:67 : term =>
  match z with
  | `(num| 0) =>
    match n with
    | `(binderIdent| _) => `(Filter.limUnder (nhdsWithin 0 (Set.Ioi 0)) fun _ => $e)
    | `(binderIdent| $n:ident) => `(Filter.limUnder (nhdsWithin 0 (Set.Ioi 0)) fun $n => $e)
    | _ => Lean.Macro.throwUnsupported
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 1003) "lim " "[" "(" n:ident " : " ty:term ")" " → " z:num "⁺" "] " e:term:67 : term =>
  match z with
  | `(num| 0) => `(Filter.limUnder (nhdsWithin (0 : $ty) (Set.Ioi (0 : $ty))) fun $n : $ty => $e)
  | _ => Lean.Macro.throwUnsupported

/-- `lim [x → 0⁻] e` — left-hand limit as `x` tends to `0` (`𝓝[<] 0`).
The type of `x` is inferred, or written `lim [(x : α) → 0⁻] e`. -/
macro:max (priority := 1003) "lim " "[" n:binderIdent " → " z:num "⁻" "] " e:term:67 : term =>
  match z with
  | `(num| 0) =>
    match n with
    | `(binderIdent| _) => `(Filter.limUnder (nhdsWithin 0 (Set.Iio 0)) fun _ => $e)
    | `(binderIdent| $n:ident) => `(Filter.limUnder (nhdsWithin 0 (Set.Iio 0)) fun $n => $e)
    | _ => Lean.Macro.throwUnsupported
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 1003) "lim " "[" "(" n:ident " : " ty:term ")" " → " z:num "⁻" "] " e:term:67 : term =>
  match z with
  | `(num| 0) => `(Filter.limUnder (nhdsWithin (0 : $ty) (Set.Iio (0 : $ty))) fun $n : $ty => $e)
  | _ => Lean.Macro.throwUnsupported

/-- `lim [x → x₀] e` — two-sided limit as `x` tends to `x₀` (`𝓝[≠] x₀`).
The type of `x` is inferred, or written `lim [(x : α) → x₀] e`.
Expands to `Filter.limUnder (nhdsWithin x₀ {x₀}ᶜ) fun x => e`.
Priority 1002 so `∞` / `0` / `0⁺` / `0⁻` still use the 1003 macros. -/
macro:max (priority := 1002) "lim " "[" n:binderIdent " → " x₀:term "] " e:term:67 : term =>
  match n with
  | `(binderIdent| _) => `(Filter.limUnder (nhdsWithin $x₀ (Set.singleton $x₀)ᶜ) fun _ => $e)
  | `(binderIdent| $n:ident) => `(Filter.limUnder (nhdsWithin $x₀ (Set.singleton $x₀)ᶜ) fun $n => $e)
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 1002) "lim " "[" "(" n:ident " : " ty:term ")" " → " x₀:term "] " e:term:67 : term =>
  `(Filter.limUnder (nhdsWithin ($x₀ : $ty) (Set.singleton ($x₀ : $ty))ᶜ) fun $n : $ty => $e)

/-- `lim [n → ∞] e = a` stands for `Tendsto (fun n => e) atTop (𝓝 a)`.
Bare `lim [n → ∞] e` remains `Filter.limUnder`. -/
macro:max (priority := 2001) "lim " "[" n:binderIdent " → " "∞" "] " e:term:67 " = " a:term:50 : term =>
  match n with
  | `(binderIdent| _) => `(Filter.Tendsto (fun _ => $e) Filter.atTop (nhds $a))
  | `(binderIdent| $n:ident) => `(Filter.Tendsto (fun $n => $e) Filter.atTop (nhds $a))
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 2001) "lim " "[" "(" n:ident " : " ty:term ")" " → " "∞" "] " e:term:67 " = " a:term:50 : term =>
  `(Filter.Tendsto (fun $n : $ty => $e) Filter.atTop (nhds $a))

/-- `lim [n → -∞] e = a` stands for `Tendsto (fun n => e) atBot (𝓝 a)`. -/
macro:max (priority := 2001) "lim " "[" n:binderIdent " → " "-" "∞" "] " e:term:67 " = " a:term:50 : term =>
  match n with
  | `(binderIdent| _) => `(Filter.Tendsto (fun _ => $e) Filter.atBot (nhds $a))
  | `(binderIdent| $n:ident) => `(Filter.Tendsto (fun $n => $e) Filter.atBot (nhds $a))
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 2001) "lim " "[" "(" n:ident " : " ty:term ")" " → " "-" "∞" "] " e:term:67 " = " a:term:50 : term =>
  `(Filter.Tendsto (fun $n : $ty => $e) Filter.atBot (nhds $a))

/-- `lim [x → 0] e = a` stands for `Tendsto (fun x => e) (𝓝[≠] 0) (𝓝 a)`. -/
macro:max (priority := 2001) "lim " "[" n:binderIdent " → " z:num "] " e:term:67 " = " a:term:50 : term =>
  match z with
  | `(num| 0) =>
    match n with
    | `(binderIdent| _) => `(Filter.Tendsto (fun _ => $e) (nhdsWithin 0 {0}ᶜ) (nhds $a))
    | `(binderIdent| $n:ident) => `(Filter.Tendsto (fun $n => $e) (nhdsWithin 0 {0}ᶜ) (nhds $a))
    | _ => Lean.Macro.throwUnsupported
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 2001) "lim " "[" "(" n:ident " : " ty:term ")" " → " z:num "] " e:term:67 " = " a:term:50 : term =>
  match z with
  | `(num| 0) => `(Filter.Tendsto (fun $n : $ty => $e) (nhdsWithin (0 : $ty) {(0 : $ty)}ᶜ) (nhds $a))
  | _ => Lean.Macro.throwUnsupported

/-- `lim [x → 0⁺] e = a` stands for `Tendsto (fun x => e) (𝓝[>] 0) (𝓝 a)`. -/
macro:max (priority := 2001) "lim " "[" n:binderIdent " → " z:num "⁺" "] " e:term:67 " = " a:term:50 : term =>
  match z with
  | `(num| 0) =>
    match n with
    | `(binderIdent| _) => `(Filter.Tendsto (fun _ => $e) (nhdsWithin 0 (Set.Ioi 0)) (nhds $a))
    | `(binderIdent| $n:ident) => `(Filter.Tendsto (fun $n => $e) (nhdsWithin 0 (Set.Ioi 0)) (nhds $a))
    | _ => Lean.Macro.throwUnsupported
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 2001) "lim " "[" "(" n:ident " : " ty:term ")" " → " z:num "⁺" "] " e:term:67 " = " a:term:50 : term =>
  match z with
  | `(num| 0) => `(Filter.Tendsto (fun $n : $ty => $e) (nhdsWithin (0 : $ty) (Set.Ioi (0 : $ty))) (nhds $a))
  | _ => Lean.Macro.throwUnsupported

/-- `lim [x → 0⁻] e = a` stands for `Tendsto (fun x => e) (𝓝[<] 0) (𝓝 a)`. -/
macro:max (priority := 2001) "lim " "[" n:binderIdent " → " z:num "⁻" "] " e:term:67 " = " a:term:50 : term =>
  match z with
  | `(num| 0) =>
    match n with
    | `(binderIdent| _) => `(Filter.Tendsto (fun _ => $e) (nhdsWithin 0 (Set.Iio 0)) (nhds $a))
    | `(binderIdent| $n:ident) => `(Filter.Tendsto (fun $n => $e) (nhdsWithin 0 (Set.Iio 0)) (nhds $a))
    | _ => Lean.Macro.throwUnsupported
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 2001) "lim " "[" "(" n:ident " : " ty:term ")" " → " z:num "⁻" "] " e:term:67 " = " a:term:50 : term =>
  match z with
  | `(num| 0) => `(Filter.Tendsto (fun $n : $ty => $e) (nhdsWithin (0 : $ty) (Set.Iio (0 : $ty))) (nhds $a))
  | _ => Lean.Macro.throwUnsupported

/-- `lim [x → x₀] e = a` stands for `Tendsto (fun x => e) (𝓝[≠] x₀) (𝓝 a)`.
Priority 2000 so `∞` / `0` / `0⁺` / `0⁻` still use the 2001 macros. -/
macro:max (priority := 2000) "lim " "[" n:binderIdent " → " x₀:term "] " e:term:67 " = " a:term:50 : term =>
  match n with
  | `(binderIdent| _) => `(Filter.Tendsto (fun _ => $e) (nhdsWithin $x₀ (Set.singleton $x₀)ᶜ) (nhds $a))
  | `(binderIdent| $n:ident) => `(Filter.Tendsto (fun $n => $e) (nhdsWithin $x₀ (Set.singleton $x₀)ᶜ) (nhds $a))
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 2000) "lim " "[" "(" n:ident " : " ty:term ")" " → " x₀:term "] " e:term:67 " = " a:term:50 : term =>
  `(Filter.Tendsto (fun $n : $ty => $e) (nhdsWithin ($x₀ : $ty) (Set.singleton ($x₀ : $ty))ᶜ) (nhds $a))

private def isAtTopSyntax? : Syntax → Bool
  | `(Filter.atTop) | `(atTop) => true
  | _ => false

private def isAtBotSyntax? : Syntax → Bool
  | `(Filter.atBot) | `(atBot) => true
  | _ => false

private def reprintTrim (stx : Syntax) : String :=
  match (unparenTerm? stx).reprint with
  | some s => s
  | none => toString stx

private def isNhdsWithinIdent? (stx : Syntax) : Bool :=
  stx.getId == `nhdsWithin

private def limDirOfNhdsSet? (s : Syntax) : Option Nat :=
  let t := reprintTrim s
  if t.contains "Ioi" then some 1
  else if t.contains "Iio" then some 2
  else if t.contains "ᶜ" || t.contains "compl" then some 0
  else none

private def asNhdsWithinArgs? (stx : Syntax) : Option (TSyntax `term × TSyntax `term) :=
  match unparenTerm? stx with
  | `($nw $x $s) =>
    if isNhdsWithinIdent? nw then some (x, s) else none
  | `($nw $_ $x $s) =>
    if isNhdsWithinIdent? nw then some (x, s) else none
  | `($nw $_ $_ $x $s) =>
    if isNhdsWithinIdent? nw then some (x, s) else none
  | _ => none

private def isNhdsIdent? (stx : Syntax) : Bool :=
  stx.getId == `nhds

private def asNhdsArg? (stx : Syntax) : Option (TSyntax `term) :=
  match unparenTerm? stx with
  | `($nh $a) =>
    if isNhdsIdent? nh then some a else none
  | `($nh $_ $a) =>
    if isNhdsIdent? nh then some a else none
  | `($nh $_ $_ $a) =>
    if isNhdsIdent? nh then some a else none
  | _ => none

/-- Infoview: print `Filter.limUnder … fun n ↦ e` as `lim [n → ∞] e`, `lim [x → 0] e`, … -/
@[app_unexpander Filter.limUnder]
def limUnder.unexpand : PrettyPrinter.Unexpander
  | `($_ $nw $x $s fun $n:ident => $e) =>
    if isNhdsWithinIdent? nw then
      match limDirOfNhdsSet? s with
      | some 0 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [$n:ident → 0] $e)
        else
          `(lim [$n:ident → $x:term] $e)
      | some 1 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [$n:ident → 0⁺] $e)
        else
          throw ()
      | some 2 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [$n:ident → 0⁻] $e)
        else
          throw ()
      | _ => throw ()
    else
      throw ()
  | `($_ $nw $x $s fun ($n:ident : $ty) => $e) =>
    if isNhdsWithinIdent? nw then
      match limDirOfNhdsSet? s with
      | some 0 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [($n:ident : $ty) → 0] $e)
        else
          `(lim [($n:ident : $ty) → $x:term] $e)
      | some 1 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [($n:ident : $ty) → 0⁺] $e)
        else
          throw ()
      | some 2 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [($n:ident : $ty) → 0⁻] $e)
        else
          throw ()
      | _ => throw ()
    else
      throw ()
  | `($_ $nw $x $s fun _ => $e) =>
    if isNhdsWithinIdent? nw then
      match limDirOfNhdsSet? s with
      | some 0 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [_ → 0] $e)
        else
          `(lim [_ → $x:term] $e)
      | some 1 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [_ → 0⁺] $e)
        else
          throw ()
      | some 2 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [_ → 0⁻] $e)
        else
          throw ()
      | _ => throw ()
    else
      throw ()
  | `($_ $f fun $n:ident => $e) =>
    if isAtTopSyntax? f then
      `(lim [$n:ident → ∞] $e)
    else if isAtBotSyntax? f then
      `(lim [$n:ident → -∞] $e)
    else if let some (x, s) := asNhdsWithinArgs? f then
      match limDirOfNhdsSet? s with
      | some 0 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [$n:ident → 0] $e)
        else
          `(lim [$n:ident → $x:term] $e)
      | some 1 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [$n:ident → 0⁺] $e)
        else
          throw ()
      | some 2 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [$n:ident → 0⁻] $e)
        else
          throw ()
      | _ => throw ()
    else
      throw ()
  | `($_ $f fun ($n:ident : $ty) => $e) =>
    if isAtTopSyntax? f then
      `(lim [($n:ident : $ty) → ∞] $e)
    else if isAtBotSyntax? f then
      `(lim [($n:ident : $ty) → -∞] $e)
    else if let some (x, s) := asNhdsWithinArgs? f then
      match limDirOfNhdsSet? s with
      | some 0 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [($n:ident : $ty) → 0] $e)
        else
          `(lim [($n:ident : $ty) → $x:term] $e)
      | some 1 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [($n:ident : $ty) → 0⁺] $e)
        else
          throw ()
      | some 2 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [($n:ident : $ty) → 0⁻] $e)
        else
          throw ()
      | _ => throw ()
    else
      throw ()
  | `($_ $f fun _ => $e) =>
    if isAtTopSyntax? f then
      `(lim [_ → ∞] $e)
    else if isAtBotSyntax? f then
      `(lim [_ → -∞] $e)
    else if let some (x, s) := asNhdsWithinArgs? f then
      match limDirOfNhdsSet? s with
      | some 0 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [_ → 0] $e)
        else
          `(lim [_ → $x:term] $e)
      | some 1 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [_ → 0⁺] $e)
        else
          throw ()
      | some 2 =>
        if isZeroSyntax? (unparenTerm? x) then
          `(lim [_ → 0⁻] $e)
        else
          throw ()
      | _ => throw ()
    else
      throw ()
  | _ =>
    throw ()

/-- Infoview: print `Tendsto (fun x => e) (𝓝[≠] x₀) (𝓝 a)` as `lim [x → x₀] e = a`. -/
@[app_unexpander Filter.Tendsto]
def tendstoLim.unexpand : PrettyPrinter.Unexpander
  | `($_ $f $l $na) =>
    if let some a := asNhdsArg? na then
      match f with
      | `(fun $n:ident => $e) =>
        if isAtTopSyntax? l then
          `(lim [$n:ident → ∞] $e = $a)
        else if isAtBotSyntax? l then
          `(lim [$n:ident → -∞] $e = $a)
        else if let some (x, s) := asNhdsWithinArgs? l then
          match limDirOfNhdsSet? s with
          | some 0 =>
            if isZeroSyntax? (unparenTerm? x) then
              `(lim [$n:ident → 0] $e = $a)
            else
              `(lim [$n:ident → $x:term] $e = $a)
          | some 1 =>
            if isZeroSyntax? (unparenTerm? x) then
              `(lim [$n:ident → 0⁺] $e = $a)
            else
              throw ()
          | some 2 =>
            if isZeroSyntax? (unparenTerm? x) then
              `(lim [$n:ident → 0⁻] $e = $a)
            else
              throw ()
          | _ => throw ()
        else
          throw ()
      | `(fun ($n:ident : $ty) => $e) =>
        if isAtTopSyntax? l then
          `(lim [($n:ident : $ty) → ∞] $e = $a)
        else if isAtBotSyntax? l then
          `(lim [($n:ident : $ty) → -∞] $e = $a)
        else if let some (x, s) := asNhdsWithinArgs? l then
          match limDirOfNhdsSet? s with
          | some 0 =>
            if isZeroSyntax? (unparenTerm? x) then
              `(lim [($n:ident : $ty) → 0] $e = $a)
            else
              `(lim [($n:ident : $ty) → $x:term] $e = $a)
          | some 1 =>
            if isZeroSyntax? (unparenTerm? x) then
              `(lim [($n:ident : $ty) → 0⁺] $e = $a)
            else
              throw ()
          | some 2 =>
            if isZeroSyntax? (unparenTerm? x) then
              `(lim [($n:ident : $ty) → 0⁻] $e = $a)
            else
              throw ()
          | _ => throw ()
        else
          throw ()
      | `(fun _ => $e) =>
        if isAtTopSyntax? l then
          `(lim [_ → ∞] $e = $a)
        else if isAtBotSyntax? l then
          `(lim [_ → -∞] $e = $a)
        else if let some (x, s) := asNhdsWithinArgs? l then
          match limDirOfNhdsSet? s with
          | some 0 =>
            if isZeroSyntax? (unparenTerm? x) then
              `(lim [_ → 0] $e = $a)
            else
              `(lim [_ → $x:term] $e = $a)
          | some 1 =>
            if isZeroSyntax? (unparenTerm? x) then
              `(lim [_ → 0⁺] $e = $a)
            else
              throw ()
          | some 2 =>
            if isZeroSyntax? (unparenTerm? x) then
              `(lim [_ → 0⁻] $e = $a)
            else
              throw ()
          | _ => throw ()
        else
          throw ()
      | _ =>
        throw ()
    else
      throw ()
  | _ =>
    throw ()

export ArchimedeanClass (stdPart)
