; =============================================================================
; Detect Programs, one will succeed, another will fail.
; Example Program 1:
; Mat a
; Module mod
; Real time = 2
; Real answer = 2
; answer = detect(a, mod, time)
; assert(a, Mat)
; assert(temp, Int)
; assert(time, Int)
; assert(b, Real)
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
; Define MAT type.
(declare-datatypes () ((MAT Mat)))
; Define Module type.
(declare-datatypes () ((MOD Mod)))
; Define the heat function.
(declare-fun detect_func (MAT MOD Real) Real)

; Define our variables
(declare-const a MAT)
(declare-const module MOD)
(declare-const time Real)
(declare-const x Real)
(declare-const output Real)

; Ensure a positive time? Is this necessary?
(assert (> time 0))
; Test the actual heat function.
(assert (= (detect_func a module time) output))
(check-sat)
(get-model)

; *****************************
; Begin program 2
; *****************************
;
; This errors out, as it should
(assert (= (detect_func a module time) a))

(check-sat)
