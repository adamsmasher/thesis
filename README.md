Soundness of Information Flow Typing in Coq
===========================================

## Abstract

Secure systems should carefully control the dependency of
low-security public data on high-security secret values,
lest an attacker be able to infer information about the secrets.
"Information flow analysis" refers to mechanisms that determine
how data may depend on other data in a program and verifies these
dependencies against an information flow security policy.
Languages and type systems can be and have been developed to track
information flow and check for policy violations; however, each
new type system must be proven correct, necessitating burdensome
boilerplate proofs.

We are developing a Coq-based formalization of an approach, devised by
Pottier and Conchon, for extending an arbitrary type system satisfying
certain criteria with information flow sensitivity. Existing proofs of the
type system's correctness can then be reused without modification, giving
the new type system proven correctness properties almost "for free". We
also hope to extend Pottier and Conchon's original design
to accommodate a broader spectrum of programming language features,
such as mutable references.
