import stdlib.Slice
open Lean

/--
mimic the PHP Array API
[array_slice][https://www.php.net/manual/en/function.array-slice.php]
-/
def List.array_slice (L : List α) (start : Nat) (size : Nat) : List α :=
  (take (size) ∘ drop start) L

/--
mimic the JavaScript Array API
[Array.prototype.slice](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/slice)
-/
def List.slice (L : List α) (start : Nat) (stop : Nat) : List α :=
  L.array_slice start (stop - start)

def List.getSlice (L : List α) (slice : Slice) : List α :=
  (slice.toList L.length).map fun i => L[i]

class IsConstant (T : Type v) where
  is_constant : T → Prop

/--
Define the postfix operator using the type class
-/
macro x:term:min "is" "constant" : term =>
  `(IsConstant.is_constant $x)

instance : IsConstant (List α) where
  is_constant : List α → Prop
    | [] => True
    | (x0 :: X) => ∀ x ∈ X, x = x0

syntax:max term noWs "[" withoutPosition(term:60) ":]" : term
macro_rules
  | `($x[$start :]) => `(($x).getSlice ⟨($start : ℤ), (($x).length : ℤ), (1 : ℤ)⟩)

syntax:max term noWs "[:" withoutPosition(term:60) "]" : term
macro_rules
  | `($x[:$stop]) => `(($x).getSlice ⟨(0 : ℤ), ($stop : ℤ), (1 : ℤ)⟩)

syntax:max term noWs "[::" withoutPosition(term:60) "]" : term
macro_rules
  | `($x[::$step]) => `(($x).getSlice ⟨(if $step < 0 then -1 else 0 : ℤ), (if $step < 0 then -($x).length.succ else ($x).length : ℤ), ($step : ℤ)⟩)

syntax:max term noWs "[" withoutPosition(term:60) ":" withoutPosition(term:80) ":]" : term
macro_rules
  | `($x[$start :$stop]) => `(($x).getSlice ⟨($start : ℤ), ($stop : ℤ), (1 : ℤ)⟩)
  | `($x[$start :$stop :]) => `(($x).getSlice ⟨($start : ℤ), ($stop : ℤ), (1 : ℤ)⟩)

syntax:max term noWs "[:" withoutPosition(term:60) ":" withoutPosition(term:60) "]" : term
macro_rules
  | `($x[:$stop :$step]) => `(($x).getSlice ⟨(if $step < 0 then -1 else 0 : ℤ), ($stop : ℤ), ($step : ℤ)⟩)

syntax:max term noWs "[" withoutPosition(term:60) "::" withoutPosition(term:60) "]" : term
macro_rules
  | `($x[$start ::$step]) => `(($x).getSlice ⟨($start : ℤ), (if $step < 0 then -($x).length.succ else ($x).length : ℤ), ($step : ℤ)⟩)

syntax:max term noWs "[" withoutPosition(term:60) ":" withoutPosition(term:60) ":" withoutPosition(term:60) "]" : term
macro_rules
  | `($x[$start :$stop :$step]) => `(($x).getSlice ⟨($start : ℤ), ($stop : ℤ), ($step : ℤ)⟩)

private partial def Slice.natLitValue? : Syntax → Option Nat
  | `(($n:num)) => some n.getNat
  | `(($n:num : $_)) => some n.getNat
  | `($n:num) => some n.getNat
  | `(OfNat.ofNat $_ $n $_) => natLitValue? n
  | `(Int.ofNat $n) => natLitValue? n
  | _ => none

/-- Infoview: print `getSlice` as Python `base[start:stop:step]`. -/
def Slice.getSliceUnexpand : PrettyPrinter.Unexpander
  | `($_ $x (Slice.mk $start $stop $step))
  | `($_ $x ⟨$start, $stop, $step⟩) =>
    let startZero := natLitValue? start == some 0
    let stepOne := natLitValue? step == some 1
    if stepOne then
      if startZero then
        `($x[:$stop])
      else
        `($x[$start :$stop])
    else if startZero then
      `($x[:$stop :$step])
    else
      `($x[$start :$stop :$step])
  | _ =>
    throw ()

@[app_unexpander List.getSlice]
def List.getSlice.unexpand := Slice.getSliceUnexpand

declare_syntax_cat slice_arg
syntax withoutPosition(term:60) : slice_arg
syntax withoutPosition(term:60) ":" : slice_arg
syntax ":" withoutPosition(term:60) : slice_arg
syntax "::" withoutPosition(term:60) : slice_arg
syntax withoutPosition(term:60) ":" withoutPosition(term:60) : slice_arg
syntax withoutPosition(term:60) ":" withoutPosition(term:60) ":" : slice_arg
syntax ":" withoutPosition(term:60) ":" withoutPosition(term:60) : slice_arg
syntax withoutPosition(term:68) "::" withoutPosition(term:60) : slice_arg
syntax withoutPosition(term:60) ":" withoutPosition(term:60) ":" withoutPosition(term:60) : slice_arg
syntax:max term noWs "[" slice_arg "," slice_arg,+ "]" : term
macro_rules
  | `($x[ $first, $rest,* ]) => do
    let indices := #[first] ++ rest
    let mut x := x
    for idx in indices do
      x ←
        match idx with
        | `(slice_arg| $t:term) =>
          `($x[$t])
        | `(slice_arg| $start:term :) =>
          `($x[$start :])
        | `(slice_arg| :$stop) =>
          `($x[:$stop])
        | `(slice_arg| ::$step) =>
          `($x[::$step])
        | `(slice_arg| $start:term : $stop)
        | `(slice_arg| $start:term : $stop :) =>
          `($x[$start :$stop])
        | `(slice_arg| : $stop:term : $step) =>
          `($x[: $stop :$step])
        | `(slice_arg| $start:term :: $step:term) =>
          `($x[$start :: $step])
        | `(slice_arg| $start:term : $stop : $step)  =>
          `($x[$start :$stop :$step])
        | _ =>
          Macro.throwUnsupported
    return x

def List.enumerate (a : List α) : List (Fin a.length × α) :=
  List.range a.length |>.pmap
    (
      fun i hi =>
        let i : Fin a.length := ⟨i, (List.mem_range (n := a.length) (m := i)).mp hi⟩
        ⟨i, a[i]⟩
    )
    (by simp)

def List.swap (a : List α) (i : Nat) (j : Nat) : List α :=
  if i = j then
    a
  else if h_lt : i < j then
    if h_j : j < a.length then
      -- a[:i] ++ [a[i]] ++ a[i + 1:j] ++ [a[j]] ++ a[j + 1:], transform to:
      -- a[:i] ++ [a[j]] ++ a[i + 1:j] ++ [a[i]] ++ a[j + 1:]
      a.take i ++ a[j] :: a.slice (i + 1) j ++ a[i] :: a.drop (j + 1)
    else
      a
  else -- j < i
    if h_i : i < a.length then
      -- a[:j] ++ [a[j]] ++ a[j + 1:i] ++ [a[i]] ++ a[i + 1:], transform to:
      -- a[:j] ++ [a[i]] ++ a[j + 1:i] ++ [a[j]] ++ a[i + 1:]
      a.take j ++ a[i] :: a.slice (j + 1) i ++ a[j] :: a.drop (i + 1)
    else
      a

def List.permute (a : List α) (i : Fin a.length) (d : ℤ) : List α :=
  match d with
  | .ofNat d =>
    let d := d.succ
    -- a[:i] ++ [a[i]] ++ a[i + 1:i + d] ++ a[i + d:], transform to:
    -- a[:i] ++ a[i + 1:i + d] ++ [a[i]] ++ a[i + d:]
    a.take i ++ a.slice (i + 1) (i + d) ++ a[i] :: a.drop (i + d)
  | .negSucc d =>
    -- a[:i - d] ++ a[i - d:i] ++ [a[i]] ++ a[i + 1:], transform to:
    -- a[:i - d] ++ [a[i]] ++ a[i - d:i] ++ a[i + 1:]
    let d := d.succ
    a.take (i - d) ++ a[i] :: a.slice (i - d) i ++ a.drop (i + 1)

def List.repeat (a : List α) (n : ℕ) : List α :=
  (List.replicate n a).flatten

/--
[itertools.product](https://docs.python.org/3/library/itertools.html#itertools.product) in Lean 4
-/
def itertools.product (lists : List (List α)) : List (List α) :=
  lists.foldr
    (fun xs acc =>
      xs.flatMap (fun x =>
        acc.map (fun tail =>
          x :: tail
        )
      )
    )
    [[]]

def List.cartesianProduct (shape : List ℕ) : List (List ℕ) :=
  itertools.product (shape.map List.range)

/--
Mimics JavaScript's [Array.splice](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/splice) and PHP's [array_splice](https://www.php.net/manual/en/function.array-splice.php) functions.
Removes `deleteCount` elements starting from `start` index and inserts `items` at that position.
Returns the modified list.

Arguments:
- `list`: The input list to modify
- `start`: The index at which to start changing the list (0-based)
- `deleteCount`: The number of elements to remove
- `items`: The elements to insert at the start position

Examples:
- `[1, 2, 3, 4].array_splice 1 2 [9, 10]` => `[1, 9, 10, 4]`
-/
def List.splice (list : List α) (start : Nat) (deleteCount : Nat) (items : List α) : List α :=
  let (front, back) := list.splitAt start
  front ++ items ++ (back.drop deleteCount)

@[app_unexpander List.take]
def List.take.unexpand : PrettyPrinter.Unexpander
  | `($_ $n:term $xs:term) =>
    `($xs.$(mkIdent `take) $n)
  | _ =>
    throw ()

@[app_unexpander List.drop]
def List.drop.unexpand : PrettyPrinter.Unexpander
  | `($_ $n:term $xs:term) =>
    `($xs.$(mkIdent `drop) $n)
  | _ =>
    throw ()
