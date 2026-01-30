;; SPDX-License-Identifier: PMPL-1.0-or-later
;; META.scm - Meta-level information for idris2-cno

(meta
  (architecture-decisions
    (adr-001
      (title "CNO as record with proof field")
      (status "accepted")
      (date "2025-01-17")
      (context "Need to pair identity functions with their proofs")
      (decision "Use Idris2 record type with function and proof fields")
      (consequences
        "Proof is always available when CNO is used"
        "Cannot create CNO without providing proof"
        "Simple API for construction and use"))

    (adr-002
      (title "Record types for proof wrappers")
      (status "accepted")
      (date "2025-01-17")
      (context "Type aliases caused inference issues with implicit bindings")
      (decision "Use record types (IdentityProof, ComposeProof) instead of type aliases")
      (consequences
        "Better type inference"
        "Explicit constructors"
        "Slightly more verbose"))

    (adr-003
      (title "Standalone library (no circular deps)")
      (status "accepted")
      (date "2025-01-17")
      (context "CNO could integrate with echidna and dyadt but would create cycles")
      (decision "Keep CNO standalone; integration modules live in dyadt")
      (consequences
        "CNO can be used independently"
        "Clean dependency graph"
        "Integration via dyadt for full ecosystem")))

  (development-practices
    (code-style "Follow Idris2 community style guide")
    (security "No unsafe operations - all proofs are verified")
    (testing "Type-level testing through compilation")
    (versioning "Semantic versioning")
    (documentation "Module-level doc comments")
    (branching "main for stable, feature/* for development"))

  (design-rationale
    (why-identity-proofs "Proves CNO operations have no side effects")
    (why-category-theory "CNOs form a trivial category with useful properties")
    (why-composition "Composing CNOs preserves the identity property")
    (why-dependent-types "Proofs are verified at compile time")))
