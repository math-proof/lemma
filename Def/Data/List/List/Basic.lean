import Def.Data.List.List
import Def.Data.List.Slice
import Structure.Fun
import Notation.Fun
import Syntax.Data.List.List

open Lean

/-- Python's open-ended slice `f[t:]` of an infinite sequence `f : ℕ → α`: the shifted sequence
`k ↦ f (t + k)`, again of type `ℕ → α` (so e.g. `(fun k ↦ γ ^ k) @ r[t:] = ∑' k, γ ^ k * r (t + k)`). -/
def Function.getSliceFrom (f : ℕ → α) (t : ℕ) : ℕ → α := fun k ↦ f (t + k)

open Elab Term Meta in
/-- `x[start:]`: for a sequence `x : ℕ → α` it is `Function.getSliceFrom x start : ℕ → α`; for any
other receiver (lists, vectors, tensors, …) it is `x.getSlice ⟨start, x.length, 1⟩` as before.
The receiver's type is inspected (without committing the elaboration) to choose the expansion. -/
@[term_elab «term__[_:]»]
def Slice.elabGetSliceFrom : TermElab := fun stx expectedType? =>
  match stx with
  | `($x[$start :]) => do
    let saved ← saveState
    let ty? ← try
        let e ← withoutErrToSorry <| elabTerm x none
        pure (some (← whnfR (← instantiateMVars (← inferType e))))
      catch _ => pure none
    saved.restore
    if let some ty := ty? then
      if ty.isMVar then tryPostpone
    let isFun := match ty? with
      | some (.app (.app (.const n _) d) _) =>
          n == ``Fun && d.isConstOf ``Nat
      | _ => false
    -- Yield to Fun.elabGetSliceFrom for Fun N _.
    if isFun then throwUnsupportedSyntax
    let isSeq := match ty? with
      | some (.forallE _ d b _) => d.isConstOf ``Nat && !b.hasLooseBVars
      | _ => false
    if isSeq then
      elabTerm (← `(Function.getSliceFrom $x ($start))) expectedType?
    else
      elabTerm (← `(($x).getSlice ⟨($start : ℤ), (($x).length : ℤ), (1 : ℤ)⟩)) expectedType?
  | _ => throwUnsupportedSyntax

/-- Infoview: print `Function.getSliceFrom f t` as `f[t:]`. -/
@[app_unexpander Function.getSliceFrom]
def Function.getSliceFrom.unexpand : PrettyPrinter.Unexpander
  | `($_ $f $t) => `($f[$t :])
  | `($_ $f $t $k) => `($f[$t :] $k)
  | _ => throw ()

partial def Slice.natLitValue? : Syntax → Option Nat
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

def List.enumerate (s : List α) : List (Fin s.length × α) :=
  List.range s.length |>.pmap
    (
      fun i hi =>
        let i : Fin s.length := ⟨i, (List.mem_range (n := s.length) (m := i)).mp hi⟩
        ⟨i, s[i]⟩
    )
    (by simp)

def List.permute (s : List α) (i : Fin s.length) (d : ℤ) : List α :=
  match d with
  | .ofNat d =>
    let d := d.succ
    -- s[:i] ++ [s[i]] ++ s[i + 1:i + d] ++ s[i + d:], transform to:
    -- s[:i] ++ s[i + 1:i + d] ++ [s[i]] ++ s[i + d:]
    s.take i ++ s.slice (i + 1) (i + d) ++ s[i] :: s.drop (i + d)
  | .negSucc d =>
    -- s[:i - d] ++ s[i - d:i] ++ [s[i]] ++ s[i + 1:], transform to:
    -- s[:i - d] ++ [s[i]] ++ s[i - d:i] ++ s[i + 1:]
    let d := d.succ
    s.take (i - d) ++ s[i] :: s.slice (i - d) i ++ s.drop (i + 1)

def List.repeat (s : List α) (n : ℕ) : List α :=
  (List.replicate n s).flatten

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

