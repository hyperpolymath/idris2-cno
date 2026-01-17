;; SPDX-License-Identifier: MPL-2.0
;; NEUROSYM.scm - Symbolic semantics for idris2-cno

(define-module (idris2-cno neurosym)
  #:export (operation-definitions proof-obligations composition-rules))

(define operation-definitions
  '((cno-construct
     (forward-semantics . "Create CNO from function and identity proof")
     (inverse . #f)
     (claim-type . "verified")
     (entropy-contribution . 0)
     (idris-type . "(f : a -> a) -> ((x : a) -> f x = x) -> CNO a")
     (proof-obligation . "identity-proof-required"))

    (cno-apply
     (forward-semantics . "Apply CNO to value, returning same value")
     (inverse . "cno-apply")
     (claim-type . "verified")
     (entropy-contribution . 0)
     (idris-type . "CNO a -> a -> a")
     (invariant . "forall x. apply cno x = x"))

    (cno-compose
     (forward-semantics . "Compose two CNOs into one CNO")
     (inverse . "cno-compose")
     (claim-type . "verified")
     (entropy-contribution . 0)
     (idris-type . "CNO a -> CNO a -> CNO a")
     (invariant . "compose cno1 cno2 is also identity"))

    (trivial-cno
     (forward-semantics . "The canonical CNO: id with Refl proof")
     (inverse . "trivial-cno")
     (claim-type . "verified")
     (entropy-contribution . 0)
     (idris-type . "CNO a"))))

(define proof-obligations
  '((identity-proof
     (description . "Every CNO must prove f(x) = x for all x")
     (verification-method . "type-level-proof-term")
     (failure-action . "reject-construction")
     (idris-encoding . "(x : a) -> f x = x"))

    (composition-preservation
     (description . "Composing CNOs preserves the identity property")
     (verification-method . "proof-composition")
     (failure-action . "reject-composition")
     (theorem . "compose-preserves-identity"))

    (category-laws
     (description . "CNOs satisfy category identity and associativity laws")
     (verification-method . "proven-in-Category-module")
     (theorems . ("left-identity" "right-identity" "associativity")))))

(define composition-rules
  '((sequential
     (rule . "verified-always")
     (reason . "CNO >>> CNO = CNO (proven)")
     (example . "cno1 >>> cno2: verified"))
    (parallel
     (rule . "verified-always")
     (reason . "CNO *** CNO = CNO on pairs (proven)")
     (example . "cno1 *** cno2: verified"))
    (n-ary
     (rule . "verified-always")
     (reason . "composeN n cno = CNO (proven by induction)")
     (example . "composeN 100 idCNO: verified"))))
