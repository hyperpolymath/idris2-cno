; SPDX-License-Identifier: MPL-2.0
; ECOSYSTEM.scm - Project ecosystem positioning

(ecosystem
  (version "1.0")
  (name "idris2-cno")
  (type "library")
  (purpose "Certified Null Operations with dependent type proofs")

  (position-in-ecosystem
    "The dependent types implementation of absolute-zero CNO concepts"
    "Bridges formal verification theory with practical Idris2 code"
    "Provides certified no-op operations with compile-time proofs"
    "Final destination for verification in the Idris2 stack")

  (ecosystem-diagram
    "
    ┌─────────────────────────────────────────────────────────────┐
    │                    User Applications                         │
    └─────────────────────────────────────────────────────────────┘
                                 │
         ┌───────────────────────┼───────────────────────┐
         ▼                       ▼                       ▼
    ┌─────────┐           ┌─────────────┐         ┌─────────┐
    │idris2-  │           │ idris2-     │         │idris2-  │
    │ dyadt   │──────────►│ echidna     │◄────────│  cno    │
    │(claims) │           │ (provers)   │         │(CNOs)   │◄─┐
    └─────────┘           └─────────────┘         └─────────┘  │
         │                                              ▲      │
         └──────────────────────────────────────────────┘      │
                                                               │
                                                    ┌──────────┴───┐
                                                    │ absolute-zero │
                                                    │   (theory)    │
                                                    └───────────────┘
    ")

  (related-projects
    (absolute-zero
      (relationship "theoretical-foundation")
      (integration "Proof ports from Coq/Lean4/Agda/Isabelle/Mizar")
      (description "CNO proofs in multiple proof assistants"))
    (aletheia
      (relationship "research-sibling")
      (integration "Reversibility concepts")
      (description "Reversible operations theory this connects to"))
    (idris2-dyadt
      (relationship "upstream-provider")
      (integration "CNO.Integration.Dyadt module")
      (description "Compile-time claims that can verify CNO properties"))
    (idris2-echidna
      (relationship "proof-backend")
      (integration "CNO.Integration.Echidna module")
      (description "Theorem prover bindings for complex CNO proofs"))
    (did-you-actually-do-that
      (relationship "ecosystem-ancestor")
      (integration "Conceptual patterns")
      (description "Rust runtime verification; CNOs are the formal dual")))

  (integration-points
    (provides
      "CNO type with compile-time identity proof"
      "Composition operators preserving CNO property"
      "Category theory structure for CNOs"
      "Verified CNO wrappers"
      "Proof templates for echidna")
    (consumes
      "Dyadt for CNO property claims"
      "Echidna for complex CNO proofs"
      "Absolute-zero for foundational theory"))

  (what-this-is
    "CNO type bundling function with identity proof"
    "Proof combinators for constructing identity proofs"
    "Category theory formalization of CNOs"
    "Composition operators preserving CNO property"
    "Integration with dyadt claims and echidna provers"
    "Reversibility and information preservation proofs")

  (what-this-is-not
    "Not a general proof assistant (use echidna)"
    "Not for runtime verification (use dyadt or did-you-actually-do-that)"
    "Not a replacement for absolute-zero (complementary, Idris2 implementation)"
    "Not for general category theory (focused on CNO structure)"))
