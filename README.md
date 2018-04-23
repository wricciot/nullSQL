# Mechanising the Metatheory of SQL with Nulls

This repository contains the Coq development of the project *Mechanising the Metatheory of SQL with Nulls*, formalising Guagliardo and Libkin's fragment of SQL (null*SQL*)

The formalisation provides a fully mechanised semantics of SQL that can be instantiated to both Boolean and three-valued logic (3VL), and includes a verified semantic-preserving translation of queries from three-valued to Boolean logic.
This development also addresses subtle behaviours of SQL in name-handling that have been considered only superficially in other formal verification efforts.

The semantics is implemented using an abstract definition of $K$-relations; since $K$-relations lack the special treatment of null values provided by SQL, a special handling of incomplete tuples is needed to bridge the syntactic and the semantic world.

## Overview
The development consists of the following Coq scripts:

* AbstractRelation.v - an abstract definition of K-relations

* Syntax.v - language definitions of SQL tables, conditions and queries,
  including well-formedness judgments

* Tribool.v - datatype with three truth values

* Semantics.v - semantics of SQL

* Translation2V.v - verified translation of 3VL-based queries to Boolean-based
  queries.
