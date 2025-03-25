 ; --- Common Definitions ---
(declare-fun x () Int)
(declare-fun x_next () Int)

; Define the invariant: x is always non-negative and strictly decreasing.
(define-fun invariant (x Int) Bool
  (= x 0))

; Initial condition: x = 10.
(assert (= x 10))

; Define the loop guard: x > 0.
(define-fun guard (x Int) Bool
  (> x 0))

; Define the transition relation: x_next = x - 1.
(define-fun transition (x Int) Bool
  (not (= x (- x 1))))

; Define the ranking function as simply x, with argument x.
(define-fun R () Int
  (let ((x (x)))
    (+ x)))

; --- Invariant Preservation Check ---
(push)
(assert
  (forall ((x Int))
    (=> (invariant x) (guard x) (transition x))))
(check-sat)
(get-model)
(pop)

; --- Termination (Ranking Function) Check ---
(push)
(assert
  (forall ((x Int))
    (=> (guard x) (transition x))))
(check-sat)
(get-model)
(pop)

; Additional Check for Loop Termination
(assert (= R 0))