[![Typecheck](https://github.com/ben-dickinson01/cwfs/actions/workflows/typecheck.yml/badge.svg)](https://github.com/ben-dickinson01/cwfs/actions/workflows/typecheck.yml)

# Categories with Families in Agda

This project formalises the definition of a category with families (CwF) in Agda, together with the set model (more precisely, the standard model in Agda's universe `Set`), and Π-types as extra structure on a CwF, interpreted in the set model. It also formalises unityped CwFs (ucwfs), shows that every ucwf gives a CwF, and gives a model of ucwfs. It follows the definitions in Castellan, Clairambault and Dybjer's *Categories with Families: Unityped, Simply Typed, Dependently Typed* ([arXiv:1904.00827](https://arxiv.org/abs/1904.00827)): Sections 2.2 and 5.1 for CwFs, Section 3.1 for ucwfs, and Section 5.3.1 for Π-types. It sits alongside my formalisation of [Rijke's Introduction to Homotopy Type Theory](https://github.com/ben-dickinson01/rijke-intro-to-hott).

## Contents

- `Prelude.agda`: a small self-contained prelude (no standard library): a level-polymorphic identity type, `Σ` and `⊤` as records, products `_×_`, and the path operations `ap`, `tr`, `inv` and `concat`, together with `tr-const` (transport in a constant family is the identity). `_≡_` and path operations are adapted from my Rijke repository (expanded to include level polymorphism).
- `CwF.agda`: the definition of a CwF as an Agda record (Definition 1 in the paper above): a category of contexts and substitutions with a terminal object, types and terms with substitution, and context comprehension with its β- and η-laws.
- `SetModel.agda`: the set model as an instance of the record. Contexts are sets, substitutions are functions, types over Γ are families of sets indexed by Γ, terms are dependent functions, and context comprehension is the Σ-type. It also gives the set model a Π-structure, with Π interpreted as Agda's dependent function type.
- `Pi.agda`: Π-types as extra structure on a CwF (Definition 28 in the paper): a record `Π-structure`, parameterised by a CwF, with `Π`, `lam` and `app`, their β- and η-laws, and substitution laws. It also defines the lifted substitution `γ ↑ A`, the paper's `⟨γ ∘ p, q⟩`.
- `UCwF.agda`: the definition of a ucwf as an Agda record (Definition 5 in the paper; a CwF with a single type, so terms are not indexed by types), and a construction `UCwF-to-CwF` turning any ucwf into a CwF whose types over each context are given by `⊤`.
- `DValuedModel.agda`: for a fixed set `D`, the ucwf whose contexts are sets, substitutions are functions, terms over Γ are functions `Γ → D`, and context extension is `Γ × D`. Terms with n free variables are n-ary operations on `D`.

The CI type-checks every `.agda` file.

## Design choices

- All code is checked with `--without-K` and `--safe`, so there are no postulates.
- The record is parameterised by four universe levels, one each for contexts, substitutions, types and terms, since in the set model the types over a context are `Γ → Set`, which lives in `Set₁`.
- The equations are propositional equalities. The equations between terms only typecheck after transporting along the corresponding equation between types. Unlike the paper, the record does not require substitutions, types or terms to form h-sets.
- `Σ` and `⊤` are records, so they have definitional η. As a result, every equation in the set model holds by `refl`, including the uniqueness of the map into the terminal context, the η-law for comprehension, and the laws for Π-types. The same holds for the `D`-valued model.
- In a ucwf terms are not indexed by types, so none of its equations need transport. Going from a ucwf to a CwF, the type-level paths are trivial because `⊤` has η, and every CwF law follows directly from a ucwf law except the β-law for `q`: its transport is along a path built from a ucwf equation, so it is removed with `tr-const`.
- Π-types are a separate record rather than fields of the CwF record, so that CwFs without Π-types (such as those obtained from ucwfs) are unaffected. Application is unary (`Tm Γ (Π A B) → Tm (Γ ▹ A) B`), which is interdefinable with the paper's binary form and makes β and η hold without transport. The lifted substitution needs one transport, and the substitution law for `lam` is transported along the one for `Π`.

## Possible future steps

- Add Σ-types, which use the same lifted substitution as Π-types.

## Use of AI

Generative AI (Claude) has been used for setting up CI and tooling, clarifying parts of the paper and asking related questions to help understanding. All of the mathematics and Agda code was written by me.

Tested with Agda 2.8.0.
