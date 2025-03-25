 ; --- Common Definitions ---
(declare-fun x () Int)
(declare-fun x_next () Int)

; Define the invariant: x is always non-negative and strictly decreasing.
(define-fun invariant () Bool
  (and (= x 0) (or (< x 1))))

; Initial condition: x = 10.
(assert (= x 10))

; Define the loop guard: x > 0.
(define-fun guard () Bool
  (> x 0))

; Define the transition relation: x_next = x - 1.
(define-fun transition () Bool
  (not (= x (- x 1))))

; Define the ranking function as simply x, with argument x.
(define-fun R () Int

; --- Invariant Preservation Check ---
(push)
(assert
  (forall ((x Int) (x_next Int))
    (=> (and (invariant) (guard) (transition))
        (invariant))))
(check-sat)
(get-model)
(pop)

; --- Termination (Ranking Function) Check ---
(push)
(assert
  (forall ((x Int) (x_next Int))
    (=> (and (guard) (transition))
        (not (< x x_next)))))
(check-sat)
(get-model)
(pop)

; Additional Check for Loop Termination
(assert (> R))