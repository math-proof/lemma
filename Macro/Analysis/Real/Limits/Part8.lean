import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Def.Analysis.Real.Limits.Part3
open Lean
open scoped Topology


/-- `lim [x → x₀⁺] e` — right-hand limit as `x` tends to `x₀` (`𝓝[>] x₀`).
Also `lim [x → 0⁺] e`. Written `lim [(x : α) → x₀⁺] e` to ascribe the binder. -/
macro:max (priority := 1003) "lim " "[" n:binderIdent " → " x₀:limPt "⁺" "] " e:term:67 : term =>
  let x₀ := termOfLimPt x₀
  match n with
  | `(binderIdent| _) => `(Filter.limUnder (nhdsWithin $x₀ (Set.Ioi $x₀)) fun _ => $e)
  | `(binderIdent| $n:ident) => `(Filter.limUnder (nhdsWithin $x₀ (Set.Ioi $x₀)) fun $n => $e)
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 1003) "lim " "[" "(" n:ident " : " ty:term ")" " → " x₀:limPt "⁺" "] " e:term:67 : term =>
  let x₀ := termOfLimPt x₀
  `(Filter.limUnder (nhdsWithin ($x₀ : $ty) (Set.Ioi ($x₀ : $ty))) fun $n : $ty => $e)

/-- `lim [x → x₀⁻] e` — left-hand limit as `x` tends to `x₀` (`𝓝[<] x₀`).
Also `lim [x → 0⁻] e`. -/
macro:max (priority := 1003) "lim " "[" n:binderIdent " → " x₀:limPt "⁻" "] " e:term:67 : term =>
  let x₀ := termOfLimPt x₀
  match n with
  | `(binderIdent| _) => `(Filter.limUnder (nhdsWithin $x₀ (Set.Iio $x₀)) fun _ => $e)
  | `(binderIdent| $n:ident) => `(Filter.limUnder (nhdsWithin $x₀ (Set.Iio $x₀)) fun $n => $e)
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 1003) "lim " "[" "(" n:ident " : " ty:term ")" " → " x₀:limPt "⁻" "] " e:term:67 : term =>
  let x₀ := termOfLimPt x₀
  `(Filter.limUnder (nhdsWithin ($x₀ : $ty) (Set.Iio ($x₀ : $ty))) fun $n : $ty => $e)

/-- `lim [x → x₀] e` — two-sided limit as `x` tends to `x₀` (`𝓝[≠] x₀`).
Also `lim [x → 0] e`. The type of `x` is inferred, or written `lim [(x : α) → x₀] e`.
Expands to `Filter.limUnder (nhdsWithin x₀ {x₀}ᶜ) fun x => e`.
Priority 1002 so `∞` / `x₀⁺` / `x₀⁻` still use the 1003 macros. -/
macro:max (priority := 1002) "lim " "[" n:binderIdent " → " x₀:term "] " e:term:67 : term =>
  match n with
  | `(binderIdent| _) => `(Filter.limUnder (nhdsWithin $x₀ (@singleton _ (Set _) Set.instSingletonSet $x₀)ᶜ) fun _ => $e)
  | `(binderIdent| $n:ident) => `(Filter.limUnder (nhdsWithin $x₀ (@singleton _ (Set _) Set.instSingletonSet $x₀)ᶜ) fun $n => $e)
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 1002) "lim " "[" "(" n:ident " : " ty:term ")" " → " x₀:term "] " e:term:67 : term =>
  `(Filter.limUnder (nhdsWithin ($x₀ : $ty) (@singleton _ (Set _) Set.instSingletonSet ($x₀ : $ty))ᶜ) fun $n : $ty => $e)

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

/-- `lim [x → x₀⁺] e = a` stands for `Tendsto (fun x => e) (𝓝[>] x₀) (𝓝 a)`.
Also `lim [x → 0⁺] e = a`. -/
macro:max (priority := 2001) "lim " "[" n:binderIdent " → " x₀:limPt "⁺" "] " e:term:67 " = " a:term:50 : term =>
  let x₀ := termOfLimPt x₀
  match n with
  | `(binderIdent| _) => `(Filter.Tendsto (fun _ => $e) (nhdsWithin $x₀ (Set.Ioi $x₀)) (nhds $a))
  | `(binderIdent| $n:ident) => `(Filter.Tendsto (fun $n => $e) (nhdsWithin $x₀ (Set.Ioi $x₀)) (nhds $a))
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 2001) "lim " "[" "(" n:ident " : " ty:term ")" " → " x₀:limPt "⁺" "] " e:term:67 " = " a:term:50 : term =>
  let x₀ := termOfLimPt x₀
  `(Filter.Tendsto (fun $n : $ty => $e) (nhdsWithin ($x₀ : $ty) (Set.Ioi ($x₀ : $ty))) (nhds $a))

/-- `lim [x → x₀⁻] e = a` stands for `Tendsto (fun x => e) (𝓝[<] x₀) (𝓝 a)`.
Also `lim [x → 0⁻] e = a`. -/
macro:max (priority := 2001) "lim " "[" n:binderIdent " → " x₀:limPt "⁻" "] " e:term:67 " = " a:term:50 : term =>
  let x₀ := termOfLimPt x₀
  match n with
  | `(binderIdent| _) => `(Filter.Tendsto (fun _ => $e) (nhdsWithin $x₀ (Set.Iio $x₀)) (nhds $a))
  | `(binderIdent| $n:ident) => `(Filter.Tendsto (fun $n => $e) (nhdsWithin $x₀ (Set.Iio $x₀)) (nhds $a))
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 2001) "lim " "[" "(" n:ident " : " ty:term ")" " → " x₀:limPt "⁻" "] " e:term:67 " = " a:term:50 : term =>
  let x₀ := termOfLimPt x₀
  `(Filter.Tendsto (fun $n : $ty => $e) (nhdsWithin ($x₀ : $ty) (Set.Iio ($x₀ : $ty))) (nhds $a))

/-- `lim [x → x₀] e = a` stands for `Tendsto (fun x => e) (𝓝[≠] x₀) (𝓝 a)`.
Also `lim [x → 0] e = a`.
Priority 2000 so `∞` / `x₀⁺` / `x₀⁻` still use the 2001 macros. -/
macro:max (priority := 2000) "lim " "[" n:binderIdent " → " x₀:term "] " e:term:67 " = " a:term:50 : term =>
  match n with
  | `(binderIdent| _) => `(Filter.Tendsto (fun _ => $e) (nhdsWithin $x₀ (@singleton _ (Set _) Set.instSingletonSet $x₀)ᶜ) (nhds $a))
  | `(binderIdent| $n:ident) => `(Filter.Tendsto (fun $n => $e) (nhdsWithin $x₀ (@singleton _ (Set _) Set.instSingletonSet $x₀)ᶜ) (nhds $a))
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 2000) "lim " "[" "(" n:ident " : " ty:term ")" " → " x₀:term "] " e:term:67 " = " a:term:50 : term =>
  `(Filter.Tendsto (fun $n : $ty => $e) (nhdsWithin ($x₀ : $ty) (@singleton _ (Set _) Set.instSingletonSet ($x₀ : $ty))ᶜ) (nhds $a))

