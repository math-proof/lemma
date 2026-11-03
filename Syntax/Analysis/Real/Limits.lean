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

/-- Point in `lim[x → x₀]`, `lim[x → x₀⁺]`, `lim[x → x₀⁻]`.
`ident` covers `x₀`; `num` covers `0`. Kept off `term` so `⁺` / `⁻` are not parsed as `posPart` / `negPart`. -/
declare_syntax_cat limPt
syntax ident : limPt

syntax num : limPt

private def termOfLimPt (x : TSyntax `limPt) : TSyntax `term := ⟨x.raw[0]⟩

/-- `lim[n → ∞] e` — limit of `e` as `n` tends to `+∞` (`atTop`).
The type of `n` is inferred, or written `lim[(n : α) → ∞] e`.
Expands to `Filter.limUnder Filter.atTop fun n => e`. -/
syntax:max (name := limAtTop) (priority := 1003) "lim[" binderIdent " → " "∞" "] " term:67 : term

macro_rules (kind := limAtTop)
  | `(lim[$n:binderIdent → ∞] $e) => do
    match n with
    | `(binderIdent| _) => `(Filter.limUnder Filter.atTop fun _ => $e)
    | `(binderIdent| $n:ident) => `(Filter.limUnder Filter.atTop fun $n => $e)
    | _ => Macro.throwUnsupported

syntax:max (name := limAtTopTyped) (priority := 1003)
  "lim[" "(" ident " : " term ")" " → " "∞" "] " term:67 : term

macro_rules (kind := limAtTopTyped)
  | `(lim[($n:ident : $ty) → ∞] $e) =>
    `(Filter.limUnder Filter.atTop fun $n : $ty => $e)

/-- `lim[n → -∞] e` — limit of `e` as `n` tends to `-∞` (`atBot`). -/
syntax:max (name := limAtBot) (priority := 1003) "lim[" binderIdent " → " "-" "∞" "] " term:67 : term

macro_rules (kind := limAtBot)
  | `(lim[$n:binderIdent → -∞] $e) => do
    match n with
    | `(binderIdent| _) => `(Filter.limUnder Filter.atBot fun _ => $e)
    | `(binderIdent| $n:ident) => `(Filter.limUnder Filter.atBot fun $n => $e)
    | _ => Macro.throwUnsupported

syntax:max (name := limAtBotTyped) (priority := 1003)
  "lim[" "(" ident " : " term ")" " → " "-" "∞" "] " term:67 : term

macro_rules (kind := limAtBotTyped)
  | `(lim[($n:ident : $ty) → -∞] $e) =>
    `(Filter.limUnder Filter.atBot fun $n : $ty => $e)

/-- `lim[x → x₀⁺] e` — right-hand limit (`𝓝[>] x₀`). Also `lim[x → 0⁺] e`. -/
syntax:max (name := limRight) (priority := 1003)
  "lim[" binderIdent " → " limPt "⁺" "] " term:67 : term

macro_rules (kind := limRight)
  | `(lim[$n:binderIdent → $x₀:limPt⁺] $e) => do
    let x₀ := termOfLimPt x₀
    match n with
    | `(binderIdent| _) => `(Filter.limUnder (nhdsWithin $x₀ (Set.Ioi $x₀)) fun _ => $e)
    | `(binderIdent| $n:ident) => `(Filter.limUnder (nhdsWithin $x₀ (Set.Ioi $x₀)) fun $n => $e)
    | _ => Macro.throwUnsupported

syntax:max (name := limRightTyped) (priority := 1003)
  "lim[" "(" ident " : " term ")" " → " limPt "⁺" "] " term:67 : term

macro_rules (kind := limRightTyped)
  | `(lim[($n:ident : $ty) → $x₀:limPt⁺] $e) => do
    let x₀ := termOfLimPt x₀
    `(Filter.limUnder (nhdsWithin ($x₀ : $ty) (Set.Ioi ($x₀ : $ty))) fun $n : $ty => $e)

/-- `lim[x → x₀⁻] e` — left-hand limit (`𝓝[<] x₀`). Also `lim[x → 0⁻] e`. -/
syntax:max (name := limLeft) (priority := 1003)
  "lim[" binderIdent " → " limPt "⁻" "] " term:67 : term

macro_rules (kind := limLeft)
  | `(lim[$n:binderIdent → $x₀:limPt⁻] $e) => do
    let x₀ := termOfLimPt x₀
    match n with
    | `(binderIdent| _) => `(Filter.limUnder (nhdsWithin $x₀ (Set.Iio $x₀)) fun _ => $e)
    | `(binderIdent| $n:ident) => `(Filter.limUnder (nhdsWithin $x₀ (Set.Iio $x₀)) fun $n => $e)
    | _ => Macro.throwUnsupported

syntax:max (name := limLeftTyped) (priority := 1003)
  "lim[" "(" ident " : " term ")" " → " limPt "⁻" "] " term:67 : term

macro_rules (kind := limLeftTyped)
  | `(lim[($n:ident : $ty) → $x₀:limPt⁻] $e) => do
    let x₀ := termOfLimPt x₀
    `(Filter.limUnder (nhdsWithin ($x₀ : $ty) (Set.Iio ($x₀ : $ty))) fun $n : $ty => $e)

/-- `lim[x → x₀] e` — two-sided limit (`𝓝[≠] x₀`). Also `lim[x → 0] e`.
Priority 1002 so `∞` / `x₀⁺` / `x₀⁻` still use the 1003 syntax. -/
syntax:max (name := limAtPt) (priority := 1002) "lim[" binderIdent " → " term "] " term:67 : term

macro_rules (kind := limAtPt)
  | `(lim[$n:binderIdent → $x₀] $e) => do
    match n with
    | `(binderIdent| _) =>
      `(Filter.limUnder (nhdsWithin $x₀ (@singleton _ (Set _) Set.instSingletonSet $x₀)ᶜ) fun _ => $e)
    | `(binderIdent| $n:ident) =>
      `(Filter.limUnder (nhdsWithin $x₀ (@singleton _ (Set _) Set.instSingletonSet $x₀)ᶜ) fun $n => $e)
    | _ => Macro.throwUnsupported

syntax:max (name := limAtPtTyped) (priority := 1002)
  "lim[" "(" ident " : " term ")" " → " term "] " term:67 : term

macro_rules (kind := limAtPtTyped)
  | `(lim[($n:ident : $ty) → $x₀] $e) =>
    `(Filter.limUnder (nhdsWithin ($x₀ : $ty) (@singleton _ (Set _) Set.instSingletonSet ($x₀ : $ty))ᶜ) fun $n : $ty => $e)

/-- `lim[n → ∞] e = a` stands for `Tendsto (fun n => e) atTop (𝓝 a)`. -/
syntax:max (name := limAtTopEq) (priority := 2001)
  "lim[" binderIdent " → " "∞" "] " term:67 " = " term:50 : term

macro_rules (kind := limAtTopEq)
  | `(lim[$n:binderIdent → ∞] $e = $a) => do
    match n with
    | `(binderIdent| _) => `(Filter.Tendsto (fun _ => $e) Filter.atTop (nhds $a))
    | `(binderIdent| $n:ident) => `(Filter.Tendsto (fun $n => $e) Filter.atTop (nhds $a))
    | _ => Macro.throwUnsupported

syntax:max (name := limAtTopTypedEq) (priority := 2001)
  "lim[" "(" ident " : " term ")" " → " "∞" "] " term:67 " = " term:50 : term

macro_rules (kind := limAtTopTypedEq)
  | `(lim[($n:ident : $ty) → ∞] $e = $a) =>
    `(Filter.Tendsto (fun $n : $ty => $e) Filter.atTop (nhds $a))

/-- `lim[n → -∞] e = a` stands for `Tendsto (fun n => e) atBot (𝓝 a)`. -/
syntax:max (name := limAtBotEq) (priority := 2001)
  "lim[" binderIdent " → " "-" "∞" "] " term:67 " = " term:50 : term

macro_rules (kind := limAtBotEq)
  | `(lim[$n:binderIdent → -∞] $e = $a) => do
    match n with
    | `(binderIdent| _) => `(Filter.Tendsto (fun _ => $e) Filter.atBot (nhds $a))
    | `(binderIdent| $n:ident) => `(Filter.Tendsto (fun $n => $e) Filter.atBot (nhds $a))
    | _ => Macro.throwUnsupported

syntax:max (name := limAtBotTypedEq) (priority := 2001)
  "lim[" "(" ident " : " term ")" " → " "-" "∞" "] " term:67 " = " term:50 : term

macro_rules (kind := limAtBotTypedEq)
  | `(lim[($n:ident : $ty) → -∞] $e = $a) =>
    `(Filter.Tendsto (fun $n : $ty => $e) Filter.atBot (nhds $a))

/-- `lim[x → x₀⁺] e = a` stands for `Tendsto (fun x => e) (𝓝[>] x₀) (𝓝 a)`. -/
syntax:max (name := limRightEq) (priority := 2001)
  "lim[" binderIdent " → " limPt "⁺" "] " term:67 " = " term:50 : term

macro_rules (kind := limRightEq)
  | `(lim[$n:binderIdent → $x₀:limPt⁺] $e = $a) => do
    let x₀ := termOfLimPt x₀
    match n with
    | `(binderIdent| _) => `(Filter.Tendsto (fun _ => $e) (nhdsWithin $x₀ (Set.Ioi $x₀)) (nhds $a))
    | `(binderIdent| $n:ident) => `(Filter.Tendsto (fun $n => $e) (nhdsWithin $x₀ (Set.Ioi $x₀)) (nhds $a))
    | _ => Macro.throwUnsupported

syntax:max (name := limRightTypedEq) (priority := 2001)
  "lim[" "(" ident " : " term ")" " → " limPt "⁺" "] " term:67 " = " term:50 : term

macro_rules (kind := limRightTypedEq)
  | `(lim[($n:ident : $ty) → $x₀:limPt⁺] $e = $a) => do
    let x₀ := termOfLimPt x₀
    `(Filter.Tendsto (fun $n : $ty => $e) (nhdsWithin ($x₀ : $ty) (Set.Ioi ($x₀ : $ty))) (nhds $a))

/-- `lim[x → x₀⁻] e = a` stands for `Tendsto (fun x => e) (𝓝[<] x₀) (𝓝 a)`. -/
syntax:max (name := limLeftEq) (priority := 2001)
  "lim[" binderIdent " → " limPt "⁻" "] " term:67 " = " term:50 : term

macro_rules (kind := limLeftEq)
  | `(lim[$n:binderIdent → $x₀:limPt⁻] $e = $a) => do
    let x₀ := termOfLimPt x₀
    match n with
    | `(binderIdent| _) => `(Filter.Tendsto (fun _ => $e) (nhdsWithin $x₀ (Set.Iio $x₀)) (nhds $a))
    | `(binderIdent| $n:ident) => `(Filter.Tendsto (fun $n => $e) (nhdsWithin $x₀ (Set.Iio $x₀)) (nhds $a))
    | _ => Macro.throwUnsupported

syntax:max (name := limLeftTypedEq) (priority := 2001)
  "lim[" "(" ident " : " term ")" " → " limPt "⁻" "] " term:67 " = " term:50 : term

macro_rules (kind := limLeftTypedEq)
  | `(lim[($n:ident : $ty) → $x₀:limPt⁻] $e = $a) => do
    let x₀ := termOfLimPt x₀
    `(Filter.Tendsto (fun $n : $ty => $e) (nhdsWithin ($x₀ : $ty) (Set.Iio ($x₀ : $ty))) (nhds $a))

/-- `lim[x → x₀] e = a` stands for `Tendsto (fun x => e) (𝓝[≠] x₀) (𝓝 a)`.
Priority 2000 so `∞` / `x₀⁺` / `x₀⁻` still use the 2001 syntax. -/
syntax:max (name := limAtPtEq) (priority := 2000)
  "lim[" binderIdent " → " term "] " term:67 " = " term:50 : term

macro_rules (kind := limAtPtEq)
  | `(lim[$n:binderIdent → $x₀] $e = $a) => do
    match n with
    | `(binderIdent| _) =>
      `(Filter.Tendsto (fun _ => $e) (nhdsWithin $x₀ (@singleton _ (Set _) Set.instSingletonSet $x₀)ᶜ) (nhds $a))
    | `(binderIdent| $n:ident) =>
      `(Filter.Tendsto (fun $n => $e) (nhdsWithin $x₀ (@singleton _ (Set _) Set.instSingletonSet $x₀)ᶜ) (nhds $a))
    | _ => Macro.throwUnsupported

syntax:max (name := limAtPtTypedEq) (priority := 2000)
  "lim[" "(" ident " : " term ")" " → " term "] " term:67 " = " term:50 : term

macro_rules (kind := limAtPtTypedEq)
  | `(lim[($n:ident : $ty) → $x₀] $e = $a) =>
    `(Filter.Tendsto (fun $n : $ty => $e) (nhdsWithin ($x₀ : $ty) (@singleton _ (Set _) Set.instSingletonSet ($x₀ : $ty))ᶜ) (nhds $a))
