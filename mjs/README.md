# lemmaPath.mjs

Suggest `Lemma/` path from `lean.js` AST + README naming.

Steps:
  1. Section from typeclasses/datatypes (`TYPE_TO_SECTION`).
     Sections are data types: a folder named after a repo Prop predicate (`SolvesStateEquation`, `GeneratorMatrix`,
     `Iterates`) or a value definition (`actor_box` → `ActorBox`) is never chosen as the section; its name is only a
     hypothesis / conclusion token (files still filed there stay accepted). Repo type abbreviations score as their head
     type (`EuclideanVec` → `EuclideanSpace` = `PiLp 2` → Matrix).
     Typeclass folders (`NormedSpace`, …) likewise only keep the files already filed there; `exp (t • Q)` with
Projections of a repo-structure binder are read through their declared (co)domain types, non-scalar only: `MRP.D : Matrix S S ℝ` → Matrix, `MDP.pi : S → ProbabilityMeasure A` → Random, chained through `FiniteMDP.MRP : FiniteMRP` (fields, `extends` parents and `namespace T` defs).
     `Q : Matrix …` elsewhere is a Matrix lemma.
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

`=ᵐ` (`MEq`, sympy `Equal`) is named inline like `Eq`, which is the preferred form:
`MEqCondExp_Integral` (both sides named), `MEq_CondExp` (hole / lambda left side),
`All_MEq_CondExp` (under `∀`), bare `MEq` (both sides holes). The relation form `X.ae.Y`
(path `X/ae/Y`, e.g. `CondExpInner/ae/Inner_CondExp`) is still accepted; only the fused `AeEq…` token became `MEq…`.
Plain `∀ᵐ` statements keep the `Ae` prefix (`AeNe_0`, `AeTendsto`).

When a relation's left side ends in a binary-operator rendering (Preimage `⁻¹'`, …), a trailing `_0` would be read as that operator's second argument (Snake_Case). Prefer the constant right after the relation: `Ne0Real_Preimage` for `(M θ).real (s t ⁻¹' {x}) ≠ 0` (hole `_` for the measure; one Preimage; no trailing S). Simple `Ne_0` / `Gt_0` stay for hole left sides.
Namespaced constants (`Measure.count`) and type ascriptions do not introduce an underscore in asGiven relations: `EqMeasureCount` (accept `EqMeasure_Count`).

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

## Typeclass hierarchy

Nested Lean typeclass tree from `vue/render.vue` (`typeclass` + related consts). Empty leaf arrays are listed as bare bullets. Comments from the source note operator / number-system support.

- Field
  - CommRing — Complex, Real, Rational, Integer +-*
    - Ring
      - Semiring
        - NonUnitalSemiring
          - NonUnitalNonAssocSemiring
            - AddCommMonoid
              - AddMonoid
                - AddSemigroup
                  - Add
                - AddZeroClass
              - AddCommSemigroup
                - AddSemigroup
                  - Add
                - AddCommMagma
                  - Add
            - Distrib
              - Mul
              - Add
              - LeftDistribClass
                - Mul
                - Add
              - RightDistribClass
                - Mul
                - Add
            - MulZeroClass
              - Mul
              - Zero
          - SemigroupWithZero
            - Semigroup
              - Mul
            - MulZeroClass
              - Mul
              - Zero
        - NonAssocSemiring
          - NonUnitalNonAssocSemiring [see above]
          - MulZeroOneClass
            - MulOneClass
              - One
              - Mul
            - MulZeroClass
              - Mul
              - Zero
          - AddCommMonoidWithOne
            - AddMonoidWithOne
              - NatCast
              - AddMonoid
                - AddSemigroup
                  - Add
                - AddZeroClass
              - One
            - AddCommMonoid
              - AddMonoid
                - AddSemigroup
                  - Add
                - AddZeroClass
              - AddCommSemigroup
                - AddSemigroup
                  - Add
                - AddCommMagma
                  - Add
        - MonoidWithZero
          - Monoid — Complex, Real, Rational, Integer with +-*
            - Semigroup
              - Mul
            - MulOneClass
              - One
              - Mul
          - MulZeroOneClass [see above]
          - SemigroupWithZero [see above]
      - AddCommGroup
        - AddGroup
          - SubNegMonoid
            - AddMonoid
              - AddSemigroup
                - Add
              - AddZeroClass
            - Neg
            - Sub
        - AddCommMonoid
          - AddMonoid
            - AddSemigroup
              - Add
            - AddZeroClass
          - AddCommSemigroup
            - AddSemigroup
              - Add
            - AddCommMagma
              - Add
      - AddGroupWithOne
        - IntCast
        - AddMonoidWithOne [see above]
        - AddGroup [see above]
      - NonUnitalRing
        - NonUnitalNonAssocRing
          - AddCommGroup [see above]
          - NonUnitalNonAssocSemiring [see above]
        - NonUnitalSemiring [see above]
      - NonAssocRing
        - NonUnitalNonAssocRing [see above]
        - NonAssocSemiring
          - NonUnitalNonAssocSemiring [see above]
          - MulZeroOneClass [see above]
          - AddCommMonoidWithOne [see above]
        - AddCommGroupWithOne
          - AddCommGroup [see above]
          - AddGroupWithOne [see above]
          - AddCommMonoidWithOne [see above]
    - CommMonoid
      - Monoid [see above]
      - CommSemigroup
        - Semigroup
          - Mul
        - CommMagma
          - Mul
    - CommSemiring
      - Semiring
        - NonUnitalSemiring [see above]
        - NonAssocSemiring [see above]
        - MonoidWithZero [see above]
      - CommMonoid [see above]
    - AddCommGroupWithOne [see above]
    - NonUnitalCommRing
      - NonUnitalRing [see above]
      - NonUnitalNonAssocCommRing
        - NonUnitalNonAssocRing [see above]
        - NonUnitalNonAssocCommSemiring
          - NonUnitalNonAssocSemiring [see above]
          - CommMagma
            - Mul
  - DivisionRing
    - Ring
      - Semiring [see above]
      - AddCommGroup [see above]
      - AddGroupWithOne [see above]
      - NonUnitalRing [see above]
      - NonAssocRing [see above]
    - DivInvMonoid
      - Monoid [see above]
      - Inv
      - Div
    - DivisionSemiring
      - Semiring [see above]
      - GroupWithZero
        - MonoidWithZero [see above]
        - DivInvMonoid [see above]
        - Nontrivial
  - Semifield
    - CommSemiring [see above]
    - DivisionSemiring [see above]
    - CommGroupWithZero
      - CommMonoidWithZero — Nat/Int
        - CommMonoid [see above]
        - MonoidWithZero [see above]
      - GroupWithZero [see above]
      - DivisionCommMonoid
        - DivisionMonoid
          - DivInvMonoid [see above]
          - InvolutiveInv
            - Inv
        - CommMonoid [see above]
- LinearOrderedCommRing
  - StrictOrderedRing — Real, Rational, Integer +-*<>≤≥
    - Ring [see above]
    - OrderedAddCommGroup
      - AddCommGroup [see above]
      - PartialOrder
        - Preorder
  - LinearOrder
    - PartialOrder
      - Preorder
    - Min
    - Max
    - Ord
  - CommMonoid [see above]
- IntegerRing
- FloorRing
- Inhabited
- GetElem
- Decidable
- DecidableEq
- DecidablePred
- DecidableRel
- LE
- LT
- KroneckerDelta
