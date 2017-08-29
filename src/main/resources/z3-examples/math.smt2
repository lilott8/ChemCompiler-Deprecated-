; =============================================================================
; Mat Programs, one will succeed, another will fail.
; Example Program 1:
;
; {Int|Real} left = 2
; {Int|Real} right = 2
; {Int|Real} answer = left + right
;
; = SAT

; Example Program 2:
; Mat a
; Mat x
; x = detect(a, mod, time)
; assert(x, mod)
; = UNSAT
; =============================================================================

; *****************************
; Begin program 1
; *****************************

(declare-datatypes () ((NUM Int Real)))

; Define our variables
(declare-const left NUM)
(declare-const right NUM)

; assert that left or right are int|real and go from there?

(check-sat)
(get-model)

; *****************************
; Begin program 2
; *****************************
;
; This errors out, as it should
(assert (= (detect_func a module time) a))

(check-sat)
