(define-parameters
  (x Nat)
  (y Nat))

(def-parameter p (QInt))

(check-sat)


(assert (or (> x 0) (= y 0)) (not (= x 0)))
(assert (= y 0) (= x 0))
(assert (> x 1) (= y 0))


(define-rank-function
  (rank Nat Nat)
  (let ((r y))
    (if (< r 1) r (- r 1))))

(check-sat)


(assert (or (> x 0) (= y 0)) (not (= x 0)))

(check-sat)