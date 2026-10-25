import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic


/--
Textbook sum over the *value* of a bound sequence at a fixed index.  In probability texts one writes
`∑_{y_t} P(… y_t = y_t …)` for the sum over the states of the single coordinate `y_t`; here

* `∑ «y.bvar»[t], body` (preferred) is the plain finite sum `∑ c, body'` (over `Finset.univ` of the
  state type, inferred from `body` and needing `[Fintype _]`), where `body'` is `body` with every
  `«y.bvar»[t]` (Fun / `GetElem`) or application `«y.bvar» t` replaced by the bound variable `c`.
* `∑ «y.bvar» t, body` is the same macro with juxtaposition instead of brackets (kept for older lemmas).

It is purely syntactic: the index `t` may be any term, and an occurrence is replaced when its index /
single argument is syntactically equal to `t`.  Other occurrences of `«y.bvar»` (e.g.
`«y.bvar»[t + 1]`, `«y.bvar» (t + 1)`, or a bare `«y.bvar»`) are left alone and are then
unbound-variable errors.  The sum is *not* over functions `ℕ → Y` / `ℕ ⇀ Y`.

The body is parsed at precedence 67 (like Mathlib's `∑`).  Both syntaxes have high priority so that
`∑ a[t], f` / `∑ a t, f` are read by this macro instead of as nested sums; when the body contains no
matching occurrence at index `t`, the juxtaposition form falls back to Mathlib's `∑ a, ∑ t, f` when
`t` is an identifier.  `∑ x, f`, `∑ x ∈ s, f`, `∑ x : T, f` are not affected.
-/
syntax:67 (name := sumAtGetElem) (priority := high)
  "∑ " ident noWs "[" withoutPosition(term) "]" ", " term:67 : term

syntax:67 (name := sumAt) (priority := high)
  "∑ " ident term:max ", " term:67 : term

