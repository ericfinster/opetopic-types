# Opetopic Types

This is an Agda library which adds a primitive notion of **opetopic
type** to type theory for use in formalizing higher algebraic
structures.

## Method

One advantage of the opetopic approach to higher structures in type
theory is that the definition of opetopic types is controlled by an
infinite sequence of **polynomial monads**, a structure which is closely
linked to the interpretation of inductive types and the definition of
type theory itself.

However, attempting to define this sequence of monads internally so
far has run into coherence problems: the definition of the n-th monad
requires knowing that the 0-th monad is n-coherent.  But *stating*
that this is true already requires some kind of definition of infinite
objects, which is what we want to use opetopic types for in the first
place.  We thus end up in a vicious cycle.

To break this cycle, we will consider that the monads defining
opetopic types are *primitives* of the theory and adjust their
operations to have more reasonable normal forms.  In practice, this
can be accomplished with Agda's rewrite mechanism.

In fact, just the definition of opetopic types will not be enough to
make much progress.  One can think of the addition of opetopic types
as equipping type theory with a **type of presentations** of higher
types.  As it turns out, the theory becomes much more expressive if 
we equip type theory with a **type theory of presentations**.  Concretely, 
this means we will additionally add equations for maps between opetopic 
types as well as a universe.  One can think of this as constructing a 
kind of "internal model" of type theory.

The essential idea of the approach taken here is that the definition
of this internal model should be enough to "do" higher algebra.

## Contents

We now describe some of the contents of the library in more detail.

1. Σ and Π of opetopic types
2. The opetopic type associated to a type
3. The "fibrant replacement", turning an opetopic type into a type
4. The join of opetopic types
5. The definition of the (∞,1)-category of types
6. A proof of the equivalence between "truncated" (∞,1)-categories and
   univalent categories

