; --- Common Definitions ---
; Declare the state variable and its next state.
(declare-func x Int)
(declare-func x_next Int)

; Define the invariant: x is always greater than or equal to 1.
(define-fun invariant ((x Int)) Bool
  (>= x 1))

; Initial condition: x = 100.
(assert (= (call x) 100))

; Define the loop guard: x > 1.
(define-func guard ((x Int)) Bool
  (> (call x) 1))

; Define the transition relation: x_next = floor(x / 2).
(define-fun floor_division ((x Int)) Int
  (if (= (mod (call x) 2) 0)
      (quotient (call x) 2)
      (+ (/ (call x) 2) 1)))

; Define the ranking function as: R(x) = log2(x).
(define-fun R ((x Int)) Real
  (log2 (call x)))

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
        (and (> (R x) (R x_next)) (< (R x_next) real-infinity))))
(check-sat)
(get-model)
(pop)

; Additional checks for floor division:
(assert
  (forall ((x Int))
    (=> (> (floor_division x x) (call x)) (= (floor_division x x) (quotient (call x) 2)))))
(assert
  (forall ((x Int))
    (=> (< (+ (/ (call x) 2) 1) (floor_division x x)) (= (floor_division x x) (/ (call x) 2))))