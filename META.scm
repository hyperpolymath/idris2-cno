; SPDX-License-Identifier: MPL-2.0
; META.scm - Project meta information

(meta
  (version "1.0")
  (project "idris2-cno")

  (architecture-decisions
    (adr-001
      (status "accepted")
      (date "2025-01-17")
      (title "CNO as data type with proof field")
      (context "Need to encode CNO with proof in type system")
      (decision "Use data type with function and proof fields: MkCNO : (f : a -> a) -> (prf : (x : a) -> f x = x) -> CNO a")
      (consequences
        "Cleaner API than Sigma type"
        "Explicit proof extraction with cnoProof"
        "Show instance possible"))

    (adr-002
      (status "accepted")
      (date "2025-01-17")
      (title "believe_me for complex proofs")
      (context "Some proofs require axioms Idris2 cannot derive (e.g., reverse (reverse xs) = xs)")
      (decision "Use believe_me with documentation noting proof exists in absolute-zero")
      (consequences
        "Type-safe API"
        "Proofs need external verification"
        "Clear documentation of assumptions"))

    (adr-003
      (status "accepted")
      (date "2025-01-17")
      (title "Category theory naming conventions")
      (context "CNOs have categorical structure")
      (decision "Use standard CT names: compose, identity; plus infix >>>, <<<")
      (consequences
        "Familiar to CT-aware users"
        "Consistent with literature"
        "Infix operators for ergonomics"))

    (adr-004
      (status "accepted")
      (date "2025-01-17")
      (title "Integration modules for ecosystem")
      (context "Need to work with dyadt and echidna")
      (decision "Create Integration.Dyadt and Integration.Echidna modules")
      (consequences
        "Clean separation of concerns"
        "Optional dependencies"
        "Easy to extend"))

    (adr-005
      (status "accepted")
      (date "2025-01-17")
      (title "Proof obligations via theorem templates")
      (context "Complex CNO proofs may need external provers")
      (decision "Define ProofObligation type and theorem templates for echidna")
      (consequences
        "Can delegate complex proofs to Z3/CVC5/etc."
        "Proof-carrying CNO records external proof reference"
        "Bridges type-level and theorem-level verification")))

  (development-practices
    (code-style
      "Follow Idris2 naming conventions"
      "Use total functions where possible (%default total)"
      "Public exports explicit with 'public export'"
      "Document all public functions with ||| comments")
    (security
      "No IO in core modules"
      "Pure functional design"
      "Proofs machine-checkable where possible")
    (testing
      "Type-checking as primary test"
      "Examples module serves as integration test"
      "Property: any CNO applied to any value returns that value")
    (versioning "Semantic versioning (SemVer)")
    (documentation
      "Doc comments on all public functions"
      "README with quick start and examples"
      "Mathematical background in THEORY.adoc")
    (branching
      "main is stable"
      "feature/* for new features"
      "fix/* for bug fixes"))

  (design-rationale
    (why-dependent-types
      "CNOs require proof bundling by definition"
      "Type system enforces correctness"
      "Compile-time verification of identity property")
    (why-category-theory
      "CNOs naturally form a category (trivial category)"
      "Composition laws are fundamental to CNO definition"
      "Connects to broader mathematical framework")
    (why-idris2
      "Best dependent type language for practical use"
      "Good FFI story for ecosystem integration"
      "Active community and development"
      "Total functional programming support")
    (why-separate-from-dyadt
      "CNOs are a specific concept (identity proofs)"
      "Dyadt is general claims (many types)"
      "Separation allows focused development"
      "Can use dyadt without CNO theory and vice versa")))
