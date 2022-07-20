# Opetopic Types

This is an Agda library which adds a notion of **opetopic type** to
type theory for use in formalizing higher algebraic structures.

The overall methodology here is to strictify the equations which make
opetopic types definable.  These are essentially the equations of a
polynomial monad.  One way to view the setup is that we are defining
an internal model with exactly enough structure to give us the 
type theory of opetopic types themsevles.

The essential idea of this approach is that adding these equations
should be enough to "do" higher algebra.

The library can accomplish the following definitions:

1. Σ and Π of opetopic types
2. The opetopic type associated to a type
3. The "fibrant replacement", turning an opetopic type into a type
4. The join of opetopic types
5. The definition of the (∞,1)-category of types
6. A proof of the equivalence between "truncated" (∞,1)-categories and
   univalent categories

