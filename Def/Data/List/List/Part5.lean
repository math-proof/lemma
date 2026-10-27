import Def.Data.List.Slice
import Theorem.Data.List.List.Part2
open Lean


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

