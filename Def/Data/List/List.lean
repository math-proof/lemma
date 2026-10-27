import Def.Data.List.Slice
open Lean


/--
mimic the PHP Array API
[array_slice][https://www.php.net/manual/en/function.array-slice.php]
-/
def List.array_slice (L : List α) (start : Nat) (size : Nat) : List α :=
  (take size ∘ drop start) L

/--
mimic the JavaScript Array API
[Array.prototype.slice](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/slice)
-/
def List.slice (L : List α) (start : Nat) (stop : Nat) : List α :=
  L.array_slice start (stop - start)

def List.getSlice (L : List α) (slice : Slice) : List α :=
  (slice.range L.length).map fun i => L[i]

