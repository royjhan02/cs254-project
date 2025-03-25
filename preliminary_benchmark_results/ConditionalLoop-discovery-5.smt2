; --- Common Definitions ---
; Declare the state variable and its next state using Int.
(declare-fun x () Int)
(declare-fun x_next () Int)

; Define the invariant: x is always non-negative.
(define-fun invariant ((x Int)) Bool
  (>= x 0))

; Initial condition: x = 10.
(assert (= x 10))

; Define the loop guard: x > 0.
(define-fun guard ((x Int)) Bool
  (> x 0))

; Define a function to check if x is even or odd.
(define-fun is-even-or-odd ((x Int)) Bool
  (if (< x 1)
    (or (= x 2) false)))

; --- Invariant Preservation Check ---
(push)
(assert
  (forall ((x Int) (x_next Int))
    (=> (and (invariant x) (guard x) (is-even-or-odd x))
        (invariant x_next))))
(check-sat)
(get-model)
(pop)

; Define the transition relation:
;
; The transition is split into two cases based on whether x is even or odd.
(define-fun even_case ((x Int)) (- x 2))

(define-fun odd_case ((x Int)) (- x 1))

; Define the ranking function as simply x.
(define-fun R ((x Int)) Int)

; --- Termination (Ranking Function) Check ---
(push)
(assert
  (forall ((x Int) (x_next Int))
    (=> (and (guard x) (is-even-or-odd x))
        (and (> R x) (= R x_next))))) 
(check-sat)
(get-model)
(pop)

; Additional assertion to ensure the loop terminates:
;
; The loop should terminate when x = 0, which is not possible in this case since
; we start with x > 0. However, adding an invariant that guarantees termination will
; make the solver more efficient.
(assert (not (= R x))) 

; --- Additional Invariant ---
;
; Define a new invariant that ensures the loop terminates:
;
(define-fun terminating ((x Int)) Bool
  (< R x))

; Add this invariant to the previous invariant and update the initial condition:
;
(assert (and (invariant x) (terminating x)))
(check-sat)
(get-model)
(pop)

; --- Fix for If Constant ---


(declare-fun x () Int)
(declare-fun x_next () Int)

(define-fun invariant ((x Int)) Bool
  (>= x 0))

(assert (= x 10))

(define-fun guard ((x Int)) Bool
  (> x 0))

(define-fun is-even-or-odd ((x Int)) Bool
  (if (< x 1)
    (or (= x 2) false)))

(assert
  (forall ((x Int) (x_next Int))
    (=> (and (invariant x) (guard x) (is-even-or-odd x))
        (invariant x_next))))

(define-fun even_case ((x Int)) (- x 2))

(define-fun odd_case ((x Int)) (- x 1))

(define-fun R ((x Int)) Int)

(assert
  (forall ((x Int) (x_next Int))
    (=> (and (guard x) (is-even-or-odd x))
        (and (> R x) (= R x_next))))) 

(assert (not (= R x)))

(define-fun terminating ((x Int)) Bool
  (< R x))

(assert (and (invariant x) (terminating x)))