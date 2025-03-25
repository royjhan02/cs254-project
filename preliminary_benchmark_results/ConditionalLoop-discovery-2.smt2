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
(define-fun even_case ((x Nat)) Nat
  (if (= x 2)
      (- x 2)

(define-fun odd_case ((x Nat)) Nat
  (if (< x 1)
      (- x 1)

; Define the ranking function as simply x.
(define-fun R ((x Nat)) Nat

; --- Invariant Preservation Check ---
(push)
(assert
  (forall ((x Nat) (x_next Nat))
    (=> (and (invariant x) (guard x) (or (= x 2) (= x 1)))
        (invariant x_next))))
(check-sat)
(get-model)
(pop)

; --- Termination (Ranking Function) Check ---
(push)
(assert
  (forall ((x Nat) (x_next Nat))
    (=> (and (guard x) (or (= x 2) (= x 1)))
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
(define-fun terminating ((x Nat)) Bool
  (< R x))

; Add this invariant to the previous invariant and update the initial condition:
;
(assert (and (invariant x) (terminating x)))
(check-sat)
(get-model)
(pop)