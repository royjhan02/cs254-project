; --- Common Definitions ---
; Declare the state variable and its next state.
(declare-fun x () Int)
(declare-fun x_next () Int)

; Define the invariant: x is always greater than or equal to 1.
(define-fun invariant ((x Int)) Bool
  (>= x 1))

; Initial condition: x = 100.
(assert (= x 100))

; Define the loop guard: x > 1.
(define-fun guard ((x Int)) Bool
  (> x 1))

; Define the transition relation: x_next = floor(x / 2).
(define-fun floor_division ((x Int) (x_next Int))
(declare-const div_int Int)
(declare-const rem_int Int)
(define-fun floor_division ((x Int)) Int
  (if (= (mod x 2) 0)
      (/ div_int x)
      (/ (+ div_int 1) x)))

; Define the ranking function as: R(x) = log2(x).
(define-fun R ((x Int)) Real
  (log2 x))

; --- Invariant Preservation Check ---
(push)
(assert
  (forall ((x Int) (x_next Int))
    (=> (and (invariant x) (guard x) (floor_division x x_next))
        (invariant x_next))))
(check-sat)
(get-model)
(pop)

; --- Termination (Ranking Function) Check ---
(push)
(assert
  (forall ((x Int) (x_next Int))
    (=> (and (guard x) (floor_division x x_next))
        (and (> (R x) (R x_next)) (< (R x_next) infinity)))))
(check-sat)
(get-model)
(pop)

; Additional checks for floor division:
(assert
  (forall ((x Int))
    (=> (> (floor_division x x) x) (= (floor_division x x) div_int))))
(assert
  (forall ((x Int))
    (=> (< (+ div_int 1) (floor_division x x)) (= (floor_division x x) rem_int))))