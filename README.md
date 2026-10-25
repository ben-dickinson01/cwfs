[![Typecheck](https://github.com/ben-dickinson01/cwfs/actions/workflows/typecheck.yml/badge.svg)](https://github.com/ben-dickinson01/cwfs/actions/workflows/typecheck.yml)

# Categories with Families in Agda

This project formalises the definition of a category with family (CwF) in Agda, together with the set model. It follows the definition in Castellan, Clairambault and Dybjer's *Categories with Families: Unityped, Simply Typed, Dependently Typed* ([arXiv:1904.00827](https://arxiv.org/abs/1904.00827)), Sections 2.2 and 5.1. It sits alongside my formalisation of [Rijke's Introduction to Homotopy Type Theory](https://github.com/ben-dickinson01/rijke-intro-to-hott).

Status: in progress.

## Planned contents

- The definition of a CwF as an Agda record: a category of contexts and substitutions with a terminal object, types and terms with substitution, and context comprehension. This is Definition 1 in the paper above.
- The set model for CwFs: contexts are sets, types over Γ are families of sets indexed by Γ, terms are dependent functions, and context comprehension is the Σ-type.

## Design choices

- All code is written without axiom K (`--without-K`).
- The record is parameterised by universe levels, since in the set model the types over a context are `Γ → Set`, which lives in `Set₁`.
- Function extensionality is postulated, as in Chapter 13 of the Rijke formalisation. A cubical version would get function extensionality for free.

## Possible future steps

- Add Π-types and other type constructors to the definition and the set model.

## Use of AI

Generative AI (Claude) has been used for clarifying parts of the paper and asking related questions to help understanding. All of the mathematics and Agda code was written by me.

Tested with Agda 2.8.0
