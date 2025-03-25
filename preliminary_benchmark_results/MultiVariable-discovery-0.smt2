; --- Common Definitions ---
; Declare the state variables and their next states.
(declare-fun x () Int)
(declare-fun x_next () Int)
(declare-fun y () Int)
(declare-fun y_next () Int)

; Define the invariants: x is always non-negative and y is always even.
(define-fun invariant1 ((x Int)) Bool
  (>= x 0))

(define-fun invariant2 ((y Int)) Bool
  (mod y 2 = 0))

; Initial conditions: x = 10, y = 20.
(assert (= x 10))
(assert (= y 20))

; Define the loop guard: both x > 0 and y > 0.
(define-fun guard1 ((x Int) (y Int)) Bool
  (and (> x 0) (> y 0)))

(define-fun guard2 ((x Int) (y Int)) Bool
  (and (> x 0) (> y 0)))

; Define the transition relations: x_next = x - 1, y_next = y - 2.
(define-fun transition1 ((x Int) (x_next Int)) Bool
  (= x_next (- x 1)))

(define-fun transition2 ((y Int) (y_next Int)) Bool
  (= y_next (- y 2)))

; Define the ranking functions as: R_x(x) = 10 - x and R_y(y) = 10 - y.
(define-fun R_x ((x Int)) Int
  (- 10 x))

(define-fun R_y ((y Int)) Int
  (- 10 y))

; --- Invariant Preservation Check ---
(push)
(assert
  (forall ((x Int) (x_next Int))
    (=> (and (invariant1 x) (guard1 x) (transition1 x x_next))
        (invariant1 x_next))))
(check-sat)
(get-model)
(pop)

(assert
  (forall ((y Int) (y_next Int))
    (=> (and (invariant2 y) (guard2 y) (transition2 y y_next))
        (invariant2 y_next))))
(check-sat)
(get-model)
(pop)

; --- Termination (Ranking Function) Check ---
(push)
(assert
  (forall ((x Int) (x_next Int))
    (=> (and (guard1 x) (transition1 x x_next))
        (and (> (R_x x) (R_x x_next)) (>= (R_x x_next) 0)))))
(check-sat)
(get-model)
(pop)

(assert
  (forall ((y Int) (y_next Int))
    (=> (and (guard2 y) (transition2 y y_next))
        (and (> (R_y y) (R_y y_next)) (>= (R_y y_next) 0)))))
(check-sat)
(get-model)
(pop)
