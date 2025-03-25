; --- Common Definitions ---
; Declare the state variable and its next state.
(declare-fun x () Int)
(declare-fun x_next () Int)

; Define the invariant: x is always non-negative and strictly decreasing.
(define-fun invariant ((x Int)) Bool
  (and (= x 0) (or (< x 1))))

; Initial condition: x = 10.
(assert (= x 10))

; Define the loop guard: x > 0.
(define-fun guard ((x Int)) Bool
  (> x 0))

; Define the transition relation: x_next = x - 1.
(define-fun transition ((x Int) (x_next Int)) Bool
  (= x_next (- x 1)))

; Define the ranking function as simply x.
(define-fun R ((x Int)) Int

; --- Invariant Preservation Check ---
(push)
(assert
  (forall ((x Int) (x_next Int))
    (=> (and (invariant x) (guard x) (transition x x_next))
        (invariant x_next))))
(check-sat)
(get-model)
(pop)

; --- Termination (Ranking Function) Check ---
(push)
(assert
  (forall ((x Int) (x_next Int))
    (=> (and (guard x) (transition x x_next))
        (and (> (R x) (R x_next)) (>= (R x_next) 0)))))
(check-sat)
(get-model)
(pop)

; Additional Check for Loop Termination
(assert (= R 0))