; --- Common Definitions ---
; Declare the state variables and their next states.
(declare-fun i () Int)
(declare-fun j () Int)

; Define the invariant for i: i is always between 0 and 10.
(define-fun inv_i ((i Int)) Bool
  (and (>= i 0) (<= i 10)))

; Define the invariant for j: j is always between 0 and 4.
(define-fun inv_j ((j Int)) Bool
  (and (>= j 0) (< j 5)))

; Initial conditions: i = 0, j = 0.
(assert (= i 0))
(assert (= j 0))

; Define the loop guards:
(define-fun guard_i ((i Int)) Bool
  (< i 10))
(define-fun guard_j ((j Int)) Bool
  (< j 5))

; Define the transition relations for i and j:
(define-fun trans_i ((i Int) (i_next Int)) Bool
  (= i_next (+ i 1)))
(define-fun trans_j ((j Int) (j_next Int)) Bool
  (= j_next (+ j 1)))

; Define the reset relation for j after each iteration of i.
(define-fun reset_j ((j Int)) Bool
  (= j 0))

; Define the ranking function as: R(i) = 10 - i, and R(j) = 5 - j.
(define-fun R_i ((i Int)) Int
  (- 10 i))
(define-fun R_j ((j Int)) Int
  (- 5 j))

; --- Invariant Preservation Check ---
(push)
(assert
  (forall ((i Int) (i_next Int) (j Int) (j_next Int))
    (=> (and (inv_i i) (guard_i i) (trans_i i i_next) (inv_j j) (guard_j j) (reset_j j))
        (and (inv_i i_next) (guard_i i_next))))
(check-sat)
(get-model)
(pop)

(push)
(assert
  (forall ((i Int) (i_next Int) (j Int) (j_next Int))
    (=> (and (inv_i i) (guard_i i) (trans_i i i_next) (inv_j j) (guard_j j) (reset_j j))
        (and (inv_j j_next) (guard_j j_next))))
(check-sat)
(get-model)
(pop)

(push)
(assert
  (forall ((i Int) (i_next Int) (j Int) (j_next Int))
    (=> (and (guard_i i) (trans_i i i_next) (inv_i i_next) (inv_j j) (guard_j j) (reset_j j))
        (>= (R_i i) (R_i i_next))))
(check-sat)
(get-model)
(pop)

(push)
(assert
  (forall ((i Int) (i_next Int) (j Int) (j_next Int))
    (=> (and (guard_i i) (trans_i i i_next) (inv_i i_next) (inv_j j) (guard_j j) (reset_j j))
        (> (R_j j) (R_j j_next)))))
(check-sat)
(get-model)
(pop)

(push)
(assert
  (forall ((i Int) (i_next Int) (j Int) (j_next Int))
    (=> (and (inv_i i) (guard_i i) (trans_i i i_next) (inv_j j) (guard_j j) (reset_j j))
        (>= (R_j j) (R_j j_next))))
(check-sat)
(get-model)
(pop)