# Component Based Denotational Semantics

## Short Description

This page is a repository for the Haskell implementation of a denotational semantics component library. This implementation is part of a dissertation titled Scalable Denotational Semantics of Imperative Programming Languages which addresses the scalability problem in Denotational Semantics.

## Objective

This library addresses the scalability problem in Denotational Semantics by removing the apparent dependency on the context of constructs in the composition of their denotations. Thus, semantic definitions map the constructs of the abstract syntax of a language directly to the combination of components which model its semantics. The components encapsulate the flow of context information.

## Resources

The system is composed of three Haskell modules that implement the library. The repository includes an example and a makefile. The compiler used for tests was GHC, version 7.0.4, implementing Haskell 98 with some extensions.
