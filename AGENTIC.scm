;; SPDX-License-Identifier: MPL-2.0
;; AGENTIC.scm - AI agent gating policies for idris2-cno

(define-module (idris2-cno agentic)
  #:export (gating-policies entropy-budgets risk-classifications))

(define gating-policies
  '((default
     (mode . "permissive")
     (require-explicit-intent . #f)
     (description . "CNO operations are inherently safe - they are identity"))

    (cno-construction
     (mode . "auto-approve")
     (require-explicit-intent . #f)
     (description . "CNO construction is safe - proof required at type level")
     (reason . "Cannot construct invalid CNO without proof"))

    (cno-application
     (mode . "auto-approve")
     (require-explicit-intent . #f)
     (description . "Applying a CNO is guaranteed to return input unchanged")
     (reason . "Identity property is proven at compile time"))))

(define entropy-budgets
  '((session
     (max-entropy . 100)
     (current . 0)
     (reset-on . "session-end"))
    (operation-costs
     (cno-construct . 0)
     (cno-apply . 0)
     (cno-compose . 0)
     (proof-construct . 1)
     (file-read . 1))
    (note . "CNO operations have zero entropy - they are provably safe")))

(define risk-classifications
  '((none
     (operations . ("cno-construct" "cno-apply" "cno-compose"))
     (auto-approve . #t)
     (reason . "CNO operations are identity - cannot cause harm"))
    (low
     (operations . ("proof-construct" "category-verify"))
     (auto-approve . #t)
     (log-decision . #f))))
