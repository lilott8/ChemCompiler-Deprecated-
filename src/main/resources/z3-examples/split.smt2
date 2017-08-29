; =============================================================================
; Mix Programs, one will succeed, another will fail.
; Example Program 1:
; Mat a
; Int num = 2
; b = split(a, num)
; assert(b.size() = 2)
; = SAT

; Example Program 2:
; Mat a
; Int x
; x = split(a, num)
; assert(UNSAT)
; =============================================================================

; *****************************
; Begin program 1
; *****************************
; Define MAT type.
(declare-datatypes () ((MAT Mat)))

; Set for output from the split command.
; (... Sort_Name (Constructor) (Backing Index Type)).
(define-sort Set (T) (Array T MAT))

; Define the split function.
(declare-fun split_func (MAT Int) (Set Int))

; Define our variables
(declare-const a MAT)
(declare-const b (Set Int))
(declare-const num Int)
(declare-const x Int)

; Ensure the split-by is > 1.
(assert (> num 1))
(assert (= (split_func a num) b))
(check-sat)
(get-model)

; *****************************
; Begin program 2
; *****************************
;
; This errors out, as it should
; (assert(= (split_func a num) x))

(check-sat)
