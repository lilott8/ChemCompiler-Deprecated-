; =============================================================================
; Heat Programs, one will succeed, another will fail.
; Example Program 1:
; Mat a
; Real temp = 2
; Real time = 2
; b = heat(a, temp, time)
; assert(a, Mat)
; assert(temp, Real)
; assert(time, Real)
; assert(b, Mat)
; = SAT

; Example Program 2:
; Mat a
; Real x
; x = heat(a, temp, time)
; assert(x, Mat)
; assert(UNSAT)
; =============================================================================

; *****************************
; Begin program 1
; *****************************
; Define MAT type.
(declare-datatypes () ((MAT Mat)))

; Define the heat function.
(declare-fun heat_func (MAT Real Real) MAT)

; Define our variables
(declare-const a MAT)
(declare-const b MAT)
(declare-const time Real)
(declare-const temp Real)
(declare-const x Real)

; Ensure a positive time? Is this necessary?
(assert (> time 0))
; There is a floor to temperature, but no ceiling? Is this necessary?
(assert (> temp -459))
; Test the actual heat function.
(assert (= (heat_func a temp time) b))
(check-sat)
(get-model)

; *****************************
; Begin program 2
; *****************************
;
; This errors out, as it should
(assert (= (heat_func a temp time) x))

(check-sat)
