; --- Common Definitions ---
(declare-fun x () Int)
(declare-fun x_next () Int)

; Define a helper function for calculating floor(x/2).
(define-fun floor (/ x Int) Int
  (cond ((< x 2) x)
        (else (- x 1))))

; Define the invariant: x is always non-negative and greater than or equal to 1.
(define-fun invariant ((x Int)) Bool
  (and (> x 0) (> x 1)))

; Initial condition: x = 100.
(assert (= x 100))

; Define the loop guard: x > 1.
(define-fun guard ((x Int)) Bool
  (> x 1))

; Define the transition relation: x_next = floor(x/2).
(define-fun transition ((x Int) (x_next Int))
  (let ((q (/ x 2)))
    (= x_next q)))

; Define a new function that checks if the transition is well-defined.
(define-fun transition-well-defined? ((x Int) (x_next Int))
  (< x_next 0))

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

; --- Termination Check with Floor ---
(assert
  (forall ((x Int) (prev_x Int))
    (=> (and (guard prev_x) (transition prev_x x)) (< x prev_x)))

(check-sat)
(get-model)
(pop)