;; SPDX-License-Identifier: PMPL-1.0-or-later
;; PLAYBOOK.scm - Operational runbook for idris2-cno

(define-module (idris2-cno playbook)
  #:export (derivation-source procedures alerts))

(define derivation-source
  '((type . "derived")
    (meta-rules . (adr-001 adr-002 adr-003))
    (state-context . "v0.1.0-released")
    (timestamp . "2025-01-17T20:00:00Z")))

(define procedures
  '((build
     (description . "Build the idris2-cno package")
     (steps
       ((step 1) (action . "idris2 --build idris2-cno.ipkg") (timeout . 180))
       ((step 2) (action . "idris2 --check tests/TestCore.idr") (timeout . 120)))
     (on-failure . "abort-and-notify"))

    (install
     (description . "Install to local Idris2 package path")
     (preconditions . ("build-successful"))
     (steps
       ((step 1) (action . "idris2 --install idris2-cno.ipkg") (timeout . 120)))
     (on-failure . "abort"))

    (test
     (description . "Run compile-time CNO property verification")
     (steps
       ((step 1) (action . "idris2 --check tests/TestCore.idr") (timeout . 180)))
     (on-failure . "report-failure"))

    (verify-proofs
     (description . "Verify all CNO identity proofs compile")
     (steps
       ((step 1) (action . "idris2 --check src/CNO/Core.idr") (timeout . 60))
       ((step 2) (action . "idris2 --check src/CNO/Proof.idr") (timeout . 60))
       ((step 3) (action . "idris2 --check src/CNO/Category.idr") (timeout . 60)))
     (on-failure . "abort-proof-failure"))))

(define alerts
  '((proof-failure
     (severity . "critical")
     (channels . ("log"))
     (message . "CNO proof verification failed - identity property violated"))))
