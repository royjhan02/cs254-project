; --- Common Definitions ---
; Declare the state variable and its next state.
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

; Define the transition relation:
;
; The transition is split into two cases based on whether x is even or odd.
;
(define-fun even_case ((x Int) (x_next Int)) Bool
  (= x_next (- x 2)))

(define-fun odd_case ((x Int) (x_next Int)) Bool
  (= x_next (- x 1)))

; Define the ranking function as simply x.
(define-fun R ((x Int)) Int

; --- Invariant Preservation Check ---
(push)
(assert
  (forall ((x Int) (x_next Int))
    (=> (and (invariant x) (guard x) (or (even_case x x_next) (odd_case x x_next)))
        (invariant x_next))))
(check-sat)
(get-model)
(pop)

; --- Termination (Ranking Function) Check ---
(push)
(assert
  (forall ((x Int) (x_next Int))
    (=> (and (guard x) (or (even_case x x_next) (odd_case x x_next)))
        (and (> (R x) (R x_next)) (>= (R x_next) 0)))))
(check-sat)
(get-model)
(pop)

; Additional assertion to ensure the loop terminates:
;
; The loop should terminate when x = 0, which is not possible in this case since
; we start with x > 0. However, adding an invariant that guarantees termination will
; make the solver more efficient.
(assert (not (= x 0)))

; --- Additional Invariant ---
;
; Define a new invariant that ensures the loop terminates:
;
(define-fun terminating ((x Int)) Bool
  (< x 1))

; Add this invariant to the previous invariant and update the initial condition:
;
(assert (and (invariant x) (terminating x)))
(assert (= x 10))
(check-sat)
(get-model)
(pop)
