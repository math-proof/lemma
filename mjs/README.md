# lemmaPath.mjs

Suggest `Lemma/` path from `lean.js` AST + README naming.

Steps:
  1. Section from typeclasses/datatypes (`TYPE_TO_SECTION`).
  2. Imply from conclusion AST (root→leaf). Equality → `LHS/eq/RHS`.
  3. Prop givens same way; path order = reverse Lean order.

Usage: `node mjs/lemmaPath.mjs [--json] <path-to.lean>`

Path atoms:
  - binder leaves (`n`, `A`, …) are holes — not emitted as path segments
  - `_/eq/One` collapses to `Eq_One`, then `Eq_1` (README `Snake_Case`; Windows-safe)
  - bare segment `1` alone is spelled `One` (not `/1/`) so Windows `lake` can build

# Lemma Naming Convention

Rule of thumb: `implyCondition.of.givenCondition.givenCondition...givenCondition`

The `givenCondition`s are listed using DeBruijn, in the reverse order as indexed in lean code,
unless otherwise stated, e.g.: constructor order wherein `givenCondition`s are listed according
to the parameter order of the constructor indicated by `implyCondition`.
If `implyCondition` is a conjunction, it is written as:
`implyCondition.implyCondition...implyCondition.of.givenCondition.givenCondition...givenCondition`

## CamelCase

CamelCase is used for unary function, eg:
`LogSumExp` denotes the expression: `(exp x).sum.log`
Generally, if `F` is a unary function, and `X` is its argument, then
`FX` denote the expression: `F X`

## Snake_Case

Snake_Case is used for binary function, eg:
`Eq_Log`
Generally, if `F` is a binary function, and `Y` is its second argument, then
`F_Y` denote the expression: `F _ Y`
wherein:
- `_` (placeholder / hole) denotes the term to be inferred by Lean, i.e. any type for `X`
- `Y` is the given type for the second argument of `F`

## Apostrophe

Apostrophe is used to separate consecutive digits, eg:
`Div1'2` denotes: `1 / 2`
Apostrophe is introduced to resolve ambiguity, otherwise `1 / 2` will have to be written as:
`DivOneTwo`, etc.

## Infix Operators

Small-letter binary infix operators are short name for Capital-letter operator name, eg:

| infix operators | prefix operators | Lean class | sympy equivalent |
| :--: | :--: | :--: | :--: |
| `X.eq.Y` | `=` | `Eq` | Equal |
| `X.ne.Y` | `≠` | `Ne` | Unequal |
| `X.gt.Y` | `>` | `Gt` | Greater |
| `X.lt.Y` | `<` | `Le` | Less |
| `X.ge.Y` | `≥` | `Ge` | GreaterThan |
| `X.le.Y` | `≤` | `Le` | LessThan |
| `X.in.Y` | `∈` | `Membership` | Contains |
| `X.is.Y` | `↔` | `Iff` | Equivalent |
| `X.as.Y` | `≃` | `SEq` | -- |
| `X.ae.Y` | `=ᵐ` | `MEq` | Equal |
| `X.ou.Y` | `∨` | `Or` | Or |
| `X.et.Y` | `∧` | `And` | And |
| `X.at.Y` | `≈` | `XEq` | -- |
| `X.to.Y` | `→` | `·.stdPart = ·` | -- |
| `X.dvd.Y` | `\|` | `Dvd` | -- |
| `X.sub.Y` | `⊆` | `Subset` | Subset |
| `X.sup.Y` | `⊇` | `Superset` | Supset |
| `X.ll.Y` | `≪` | `AbsolutelyContinuous` | -- |
| `X.gg.Y` | `≫` | `CategoryStruct.comp` | -- |

## Plural S

The English Plural Letter `S` is used to denote double occurrence of types:
- `SEqSumSGet` is short for : `SumGet.as.SumGet`

## Identity

The Identity is a simplified version of an Equality/Equivalence of the same type:
- `Sum` is short for : `EqSumS` (which as rule of `Plural S`, is defined as `Sum.eq.Sum`)
- `And` is abbreviated from : `IffAndS` (which as rule of `Plural S`, is defined as `And.is.And`)

## Variadic Functions

`List`, `Finset` are considered variadic functions, eg:
- `In_ListNeg` denotes: `_ ∈ [Neg]`
- `In_Finset_AddMulS` denotes: `_ ∈ {_, AddMul, AddMul}`