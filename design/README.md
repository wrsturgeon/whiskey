# Language Design Document

Work in progress.

## Choices with probabilities they'll be net beneficial

### >2/3 confidence
- **Each file is a record**: the beginning and EOF act as opening and closing parentheses.
  - Corollary: Record syntax ought to look awfully similar to top-level definition in other languages.
  - Corollary: Record fields/projections can be public or private.
  - Corollary: Collapse "modules," "structs," and "records," if there were any distinction to begin with.
  - Corollary: Import syntax will be tough to work out, but something like Nix's `with` could work.
    - Possibly name it `use` instead (to fit with `let ...; ...`).

### 1/2-2/3 confidence
- **Any (trait?) function can be "infix"/method-style**: `f x y === x.f y`.
- **Proofs that fuzz for counterexamples**: Gonna need some explanation below.
  - A heavy-duty type system like Coq's allows us to juice every last drop out of the Curry-Howard isomorphism.
  - However, proving things by constructing terms is generally a pain in the ass.
  - To make matters worse, you can prove things if you happen upon the right sequence of steps, but
    there's generally no indication that "you won't be able to prove this thing you're working on."
  - Solution: Tree-search (A*?) mechanism that, even N steps, runs a potential counterexample on the current goal.
    - If that counterexample fails, prune the branch you're working on.
      - TODO: need to know how to save these results and/or walk back up the tree, since
        foreseeably we could be expanding nonsensical branches faster than we're cutting them
    - If all branches are cut, conclude that the statement is not provable.
      - But do *not* mark it false!

### <1/3 confidence
- **Every value comes from a typeclass/trait**.

## Resources

Type system equivalent to Coq's: <https://github.com/metacoq/metacoq#pcuic>
