[![Typecheck](https://github.com/ben-dickinson01/cwfs/actions/workflows/typecheck.yml/badge.svg)](https://github.com/ben-dickinson01/cwfs/actions/workflows/typecheck.yml)

# Categories with Families in Agda

This project formalises the definition of a category with families (CwF) in Agda, together with the set model (more precisely, the standard model in Agda's universe `Set`). It follows the definition in Castellan, Clairambault and Dybjer's *Categories with Families: Unityped, Simply Typed, Dependently Typed* ([arXiv:1904.00827](https://arxiv.org/abs/1904.00827)), Sections 2.2 and 5.1. It sits alongside my formalisation of [Rijke's Introduction to Homotopy Type Theory](https://github.com/ben-dickinson01/rijke-intro-to-hott).

## Contents

- `Prelude.agda`: a small self-contained prelude (no standard library): a level-polymorphic identity type, `Σ` and `⊤` as records, and the path operations `ap`, `tr`, `inv` and `concat`. `_≡_` and path operations are adapted from my Rijke repository (expanded to include level polymorphism). 
- `CwF.agda`: the definition of a CwF as an Agda record (Definition 1 in the paper above): a category of contexts and substitutions with a terminal object, types and terms with substitution, and context comprehension with its β- and η-laws.
- `SetModel.agda`: the set model as an instance of the record. Contexts are sets, substitutions are functions, types over Γ are families of sets indexed by Γ, terms are dependent functions, and context comprehension is the Σ-type.

`agda SetModel.agda` checks everything.

## Design choices

- All code is checked with `--without-K` and `--safe`, so there are no postulates.
- The record is parameterised by four universe levels, one each for contexts, substitutions, types and terms, since in the set model the types over a context are `Γ → Set`, which lives in `Set₁`.
- The equations are propositional equalities. The equations between terms only typecheck after transporting along the corresponding equation between types. Unlike the paper, the record does not require substitutions, types or terms to form h-sets.
- `Σ` and `⊤` are records, so they have definitional η. As a result, every equation in the set model holds by `refl`, including the uniqueness of the map into the terminal context and the η-law for comprehension.

## Possible future steps

- Add Π-types and other type constructors to the definition and the set model.

## Use of AI

Generative AI (Claude) has been used for setting up CI and tooling, clarifying parts of the paper and asking related questions to help understanding. All of the mathematics and Agda code was written by me.

Tested with Agda 2.8.0.
