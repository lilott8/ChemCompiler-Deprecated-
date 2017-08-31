; Declare the Mat object
(declare-datatypes () ((MAT Mat)))
(declare-datatypes () ((Type A B)))
; Define the mix function
(declare-fun mix (MAT MAT Real) MAT)
(declare-const a MAT)
(declare-const b MAT)
(declare-const r Real)
(assert (= (mix a b r) Mat))
; Check for satisfiability.
(check-sat)
; Get the model generated.
(get-model)
