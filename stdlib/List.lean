import stdlib.Slice


def List.substr (L : List α) (start : Nat) (size : Nat) : List α :=
  (take (size) ∘ drop start) L

def List.slice (L : List α) (start : Nat) (stop : Nat) : List α :=
  L.substr start (stop - start)

class IsConstant (T : Type v) where
  is_constant : T → Prop

-- Define the postfix operator using the type class
macro x:term:min "is" "constant" : term =>
  `(IsConstant.is_constant $x)


instance : IsConstant (List α) where
  is_constant : List α → Prop
    | [] => True
    | (x0 :: X) => ∀ x ∈ X, x = x0


instance : GetElem (List α) Slice (List α) fun _ _ => True where
  getElem a slice _ := (slice.toList a.length).map fun i => a[i]


syntax:max term noWs "[" withoutPosition(term:60) ":]" : term
macro_rules
  | `($x[$start :]) => `($x[(⟨($start : ℤ), (($x).length : ℤ), (1 : ℤ)⟩ : Slice)])

syntax:max term noWs "[" withoutPosition(term:60) ":" withoutPosition(term:100) ":]" : term
macro_rules
  | `($x[$start :$stop]) => `($x[(⟨($start : ℤ), ($stop : ℤ), (1 : ℤ)⟩ : Slice)])
  | `($x[$start :$stop :]) => `($x[(⟨($start : ℤ), ($stop : ℤ), (1 : ℤ)⟩ : Slice)])

syntax:max term noWs "[" withoutPosition(term:60) ":" withoutPosition(term:60) ":" withoutPosition(term:60) "]" : term
macro_rules
  | `($x[$start :$stop :$step]) => `($x[(⟨($start : ℤ), ($stop : ℤ), ($step : ℤ)⟩ : Slice)])

syntax:max term noWs "[" withoutPosition(term:60) "," withoutPosition(term:60) "]" : term
macro_rules
  | `($x[$i, $j]) => `($x[$i][$j])

def List.enumerate (a : List α) : List (Fin a.length × α) :=
  List.range a.length |>.pmap
    (
      fun i hi =>
        let i : Fin a.length := ⟨i, (List.mem_range (n := a.length) (m := i)).mp hi⟩
        ⟨i, a[i]⟩
    )
    (by simp)

def List.swap (a : List α) (i : Nat) (j : Nat) : List α :=
  if i == j then
    a
  else if h_lt : i < j then
    if hj : j < a.length then
      -- a[:i] ++ [a[i]] ++ a[i + 1:j] ++ [a[j]] ++ a[j + 1:], transform to:
      -- a[:i] ++ [a[j]] ++ a[i + 1:j] ++ [a[i]] ++ a[j + 1:]
      a.take i ++ a[j] :: a.slice (i + 1) j ++ a[i] :: a.drop (j + 1)
    else
      a
  else
    -- j < i
    if hi : i < a.length then
      -- a[:j] ++ [a[j]] ++ a[j + 1:i] ++ [a[i]] ++ a[i + 1:], transform to:
      -- a[:j] ++ [a[i]] ++ a[j + 1:i] ++ [a[j]] ++ a[i + 1:]
      a.take j ++ a[i] :: a.slice (j + 1) i ++ a[j] :: a.drop (i + 1)
    else
      a

-- def a : List ℕ := List.range 10 -- python: a = [*range(10)]
-- #eval a
-- #eval a[-1:-1:-1]   -- []
-- #eval a[-1:-10:-1]  -- [9, 8, 7, 6, 5, 4, 3, 2, 1]
-- #eval a[9:0:-1]     -- [9, 8, 7, 6, 5, 4, 3, 2, 1]
-- #eval a[-10:-11:-1] -- [0]
-- #eval a[0:-1:-1]    -- []
-- #eval a[-20:-9]     -- [0]
-- #eval a[1:-2:5]     -- [1, 6]
-- #eval a[0:9:2]      -- [0, 2, 4, 6, 8]
-- #eval a[-2:0:-2]    -- [8, 6, 4, 2]
-- #eval a[-2:]    -- [8, 9]
