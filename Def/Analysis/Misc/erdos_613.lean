import Mathlib
open Classical
open scoped BigOperators


-- 1. Define the main claim

/-- “Color-{name}`col` monochromatic star of size {name}`k`”: there is a center {given}`x` and a set
    {given (type := "Finset V")}`S` of {name}`k` distinct neighbors of {name}`x` such that every
    edge {given -show}`y` {lean}`s(x, y)` with {lean}`y ∈ S` is present in {lean}`G` and colored
    {name}`col`.  (No restriction on edges inside {name}`S`.) -/
def hasMonoStar {V:Type*} (G : SimpleGraph V) (color : Sym2 V → Fin 2)
    (col : Fin 2) (k : ℕ) : Prop :=
  ∃ (x : V) (S : Finset V),
    S.card = k ∧
    x ∉ S ∧
    ∀ ⦃y : V⦄, y ∈ S → G.Adj x y ∧ color (s(x, y)) = col

/--
{given -show}`a, b, c : V`
“Color-{name}`col` monochromatic triangle”: there exist {name}`a`, {name}`b`, {name}`c` with all three edges
present in {lean}`G` and colored {name}`col`.  (Adjacency already forces distinctness.)
-/
def hasMonoTriangle {V:Type*} (G : SimpleGraph V) (color : Sym2 V → Fin 2)
    (col : Fin 2) : Prop :=
  ∃ a b c : V,
    G.Adj a b ∧ G.Adj b c ∧ G.Adj a c ∧
    color (s(a, b)) = col ∧
    color (s(b, c)) = col ∧
    color (s(a, c)) = col

/-- **Statement (n = 5 case of Pikhurko’s counterexample).**
There exists a simple graph on {lean}`16` vertices with exactly {lean}`44` edges such that
for *every* 2‑coloring of unordered pairs, either color {lean (type := "Fin 2")}`0` contains a $`K_{1,5}`
(a 5‑edge star) or color {lean (type := "Fin 2")}`1` contains a $`K₃` (a triangle).

This only *states* the claim (as a {lean}`Prop`).  You can later prove it from the
explicit construction, or assume it as an axiom while you develop the rest. -/
def Pikhurko_n5_statement : Prop :=
  ∃ (V:Type) (G : SimpleGraph V),
    G.edgeSet.ncard = 44 ∧
    ∀ (color : Sym2 V → Fin 2),
      hasMonoStar G color 0 5 ∨ hasMonoTriangle G color 1

