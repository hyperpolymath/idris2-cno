;; SPDX-License-Identifier: PMPL-1.0-or-later
;; ECOSYSTEM.scm - Ecosystem relationships for idris2-cno

(ecosystem
  (version "1.0.0")
  (name "idris2-cno")
  (type "library")
  (purpose "Certified Null Operations with compile-time identity proofs")

  (position-in-ecosystem
    (role "foundation")
    (layer "proof-primitives")
    (description "Provides CNO types for verified identity operations"))

  (related-projects
    (project "idris2-dyadt"
      (relationship "consumer")
      (description "Wraps CNOs as dyadt claims for verification integration"))

    (project "idris2-echidna"
      (relationship "sibling")
      (description "Can verify CNO properties using external theorem provers"))

    (project "absolute-zero"
      (relationship "inspiration")
      (description "Original CNO concept from formal verification methodology"))

    (project "category-theory"
      (relationship "theoretical-basis")
      (description "CNOs form a trivial category where all morphisms are identity")))

  (what-this-is
    "Identity functions with compile-time proofs"
    "CNO composition with proof preservation"
    "Category-theoretic structure for CNOs"
    "Building block for verified transformations")

  (what-this-is-not
    "General function verification"
    "Runtime checking"
    "A testing framework"
    "A replacement for proper proofs of non-identity functions"))
