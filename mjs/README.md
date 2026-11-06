# lemmaPath.mjs

Suggest `Lemma/` path from `lean.js` AST + README naming.

Usage: `node mjs/lemmaPath.mjs [--json] <path-to.lean>`

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
| -- | `∧` | `And` | And |
| `X.at.Y` | `≈` | `XEq` | -- |
| `X.to.Y` | `→` | `·.stdPart = ·` | -- |
| -- | `\|` | `Dvd` | -- |
| -- | `⊆` | `Subset` | Subset |
| -- | `⊇` | `Superset` | Supset |
| `X.ll.Y` | `≪` | `AbsolutelyContinuous` | -- |
| `X.gg.Y` | `≫` | `CategoryStruct.comp` | -- |

`=ᵐ` (`MEq`, sympy `Equal`) is named inline like `Eq`, which is the preferred form:
`MEqCondExp_Integral` (both sides named), `MEq_CondExp` (hole / lambda left side),
`All_MEq_CondExp` (under `∀`), bare `MEq` (both sides holes). The relation form `X.ae.Y`
(path `X/ae/Y`, e.g. `CondExpInner/ae/Inner_CondExp`) is still accepted;


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
